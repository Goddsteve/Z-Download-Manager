const BRIDGE = "http://127.0.0.1:9420";
const POLL_MS = 2000;

// skip
const SKIP_DOMAINS = [
  "mail.google.com",
  "drive.google.com",
  "docs.google.com",
  "googleusercontent.com",
  "outlook.live.com",
  "outlook.office.com",
  "dropbox.com",
  "onedrive.live.com",
  "icloud.com",
  "mail.yahoo.com",
  "proton.me",
];

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

function hostOf(u) {
  try { return new URL(u).hostname.toLowerCase(); } catch { return ""; }
}

function isSkipped(u) {
  const host = hostOf(u);
  return !!host && SKIP_DOMAINS.some((d) => host === d || host.endsWith("." + d));
}


let lock = Promise.resolve();
function withPending(fn) {
  const run = lock.then(async () => {
    const { pending = {} } = await chrome.storage.session.get("pending");
    const result = await fn(pending);
    await chrome.storage.session.set({ pending });
    return result;
  });
  lock = run.catch(() => {});
  return run;
}


const BYPASS_MS = 10 * 60 * 1000;
const bypassMem = new Map();                                  
const norm = (u) => (u || "").split("#")[0];

async function addBypass(url) {
  const key = norm(url);
  const exp = Date.now() + BYPASS_MS;
  bypassMem.set(key, exp);
  const { bypass = {} } = await chrome.storage.session.get("bypass");
  for (const k of Object.keys(bypass)) if (bypass[k] < Date.now()) delete bypass[k];
  bypass[key] = exp;
  await chrome.storage.session.set({ bypass });
}

async function isBypassed(...urls) {
  const keys = urls.filter(Boolean).map(norm);
  if (keys.some((k) => (bypassMem.get(k) || 0) > Date.now())) return true;
  const { bypass = {} } = await chrome.storage.session.get("bypass");
  return keys.some((k) => (bypass[k] || 0) > Date.now());
}


async function collectCookies(urls) {
  const seen = new Map();
  for (const u of urls) {
    if (!u || !/^https?:\/\//i.test(u)) continue;
    try {
      for (const c of await chrome.cookies.getAll({ url: u })) {
        seen.set(c.domain + "|" + c.path + "|" + c.name, {
          name: c.name, value: c.value, domain: c.domain, path: c.path, secure: c.secure,
        });
      }
    } catch (e)
  }
  return [...seen.values()];
}


async function handOffToBrowser(id, entry) {
  try {
   
    await addBypass(entry.url);
    
    await fetch(BRIDGE + "/handoff", {
      method: "POST",
      headers: { "Content-Type": "application/json", "X-ZManager": "1" },
      body: JSON.stringify({ id }),
    }).catch(() => {});
    chrome.downloads.download({ url: entry.url, conflictAction: "uniquify" }, () => {
      if (chrome.runtime.lastError) console.log("Browser fallback failed:", chrome.runtime.lastError.message);
    });
  } catch (e) {
    console.log("Fallback error:", e);
  }
}

let watching = false;
async function watch() {
  if (watching) return;
  watching = true;
  let misses = 0;
  try {
    while (true) {
      const { pending = {} } = await chrome.storage.session.get("pending");
      const ids = Object.keys(pending);
      if (!ids.length) break;

      let statuses;
      try {
        const res = await fetch(BRIDGE + "/status?ids=" + ids.join(","), { headers: { "X-ZManager": "1" } });
        if (!res.ok) throw new Error("status " + res.status);
        statuses = await res.json();
        misses = 0;
      } catch (e) {
        
        if (++misses >= 5) { await withPending((p) => { for (const k of Object.keys(p)) delete p[k]; }); break; }
        await sleep(POLL_MS);
        continue;
      }

      for (const id of ids) {
        const st = statuses[id];
        if (st === "FAILED") {
          const entry = pending[id];
          await withPending((p) => { delete p[id]; });
          await handOffToBrowser(id, entry);
        } else if (!st || st === "COMPLETED" || st === "CANCELLED" || st === "GONE") {
          await withPending((p) => { delete p[id]; });       
        }
      }

      await sleep(POLL_MS);
      await chrome.runtime.getPlatformInfo();              
    }
  } finally {
    watching = false;
  }
}

// ---------- intercept browser downloads ----------
chrome.downloads.onCreated.addListener(async (item) => {
 
  if (item.byExtensionId && item.byExtensionId === chrome.runtime.id) return;
  if (await isBypassed(item.url, item.finalUrl)) return;

  
  if (!/^https?:\/\//i.test(item.url)) return;

  
  if (isSkipped(item.url) || isSkipped(item.finalUrl) || isSkipped(item.referrer)) return;

  const filename = (item.filename || "").split(/[\\/]/).pop();
  const cookies = await collectCookies([item.url, item.finalUrl, item.referrer]);

  try {
    const res = await fetch(BRIDGE, {
      method: "POST",
      headers: { "Content-Type": "application/json", "X-ZManager": "1" },
      body: JSON.stringify({
        url: item.url,
        referrer: item.referrer || "",
        filename,
        cookies,
        userAgent: navigator.userAgent,
      }),
    });
    if (!res.ok) throw new Error("bridge returned " + res.status);
    const { id } = await res.json();

    
    chrome.downloads.cancel(item.id, () => {
      void chrome.runtime.lastError;
      chrome.downloads.erase({ id: item.id }, () => void chrome.runtime.lastError);
    });

    
    if (id) {
      await withPending((p) => { p[id] = { url: item.url, referrer: item.referrer || "", filename, t: Date.now() }; });
      watch();
    }
  } catch (err) {
   
    console.log("Z-Manager unreachable, browser keeps the download:", err);
  }
});


chrome.alarms.create("zm-watch", { periodInMinutes: 1 });
chrome.alarms.onAlarm.addListener((a) => { if (a.name === "zm-watch") watch(); });
watch();
