# Z-Download-Manager
Alternative download manager for browsers

IMPORTANT!
put the "background.js and manifest.json" in a folder before adding it as an extension to the browser. PS i cant upload it on git with the folder sorry :<


Step 1: Add the extension to your browser

Microsoft Edge
Open edge://extensions
Turn on Developer mode (toggle at the bottom left)
Click Load unpacked
Select the extension folder (the one containing manifest.json)

Google Chrome
Open chrome://extensions
Turn on Developer mode (toggle at the top right)
Click Load unpacked
Select the extension folder
Brave / Opera / Vivaldi

Same as Chrome. Use brave://extensions, opera://extensions or vivaldi://extensions.

Firefox is not supported. The extension uses Manifest V3 service workers, which Firefox doesn't run the same way.

Step 2: Test it
Make sure Z-Manager is running. The status at the bottom should say Browser bridge ready.
Download any file in your browser.
The download is taken over by Z-Manager. Its window pops up, a sound plays, and it plays another when the file is done.
