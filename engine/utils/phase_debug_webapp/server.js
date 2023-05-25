#!/usr/bin/env node

const http = require("http");
const fs = require('fs');
const path = require('path');

const port = process.env.PORT || 8000;

let [_node, self, ...args] = process.argv;
let ROOT = path.dirname(self);

if (args.length !== 1) {
    console.log(`
Usage: ${self} [DEBUG_ENGINE_PATH]

DEBUG_ENGINE_PATH: the directory which contains the
[debug-circus-engine.json] file, that is, the directory you gave to
the option \`--debug-engine\`.

Environment variables:
 - PORT [integer]: the port on which to run the server
`.trim());
    process.exit();
}

const [DEBUG_ENGINE_PATH] = args;
const JSON_FILENAME = 'debug-circus-engine.json';

http.createServer(function(req, res) {
    let url = req.url.split('?')[0];
    let stream = (ct, path) => {
        res.writeHead(200, { 'Content-Type': ct + '; charset=utf-8' });
        fs.createReadStream(path).pipe(res);
    };
    if (url == '/index.html' || url == '/') {
        stream('text/html', ROOT + '/index.html');
    } else if (url == '/script.js') {
        stream('application/javascript', ROOT + '/script.js');
    } else if (url == '/' + JSON_FILENAME) {
        stream('application/json', DEBUG_ENGINE_PATH + '/' + JSON_FILENAME);
    } else {
        res.writeHead(404, { 'Content-Type': 'text/html' });
        res.write('Unknown route '+url);
    }
}).listen(port, () => {
    console.log(`Running on port ${port}. Please visit [http://localhost:${port}/] in your web browser.`);
});
