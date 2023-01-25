const http = require('http');
const fs = require('fs');

let args = process.argv.slice(2);

if(!args[0]){
    throw "First argument should be APP_ROOT, the directory in which the react application lives.";
}

let APP_ROOT = args[0];
let CRATE_ROOT = args[1] || process.cwd();
let PORT = 8888;

let isDir = path =>
    {try { return fs.lstatSync(path).isDirectory();
         } catch (_) { return false; }};

let man = `
  ${process.argv.slice(0, 2).join(' ')} APP_ROOT [CRATE_ROOT]
`;

if (!isDir(APP_ROOT))
    throw `APP_ROOT is [${APP_ROOT}], but this is not a directory`;
if (!isDir(CRATE_ROOT))
    throw `CRATE_ROOT is [${CRATE_ROOT}], but this is not a directory`;


const { resolve } = require('path');
let getFiles = dir =>
    Array.prototype.concat(...fs.readdirSync(dir, { withFileTypes: true }).map(dirent => {
        const res = resolve(dir, dirent.name);
        return dirent.isDirectory() ? getFiles(res) : res;
    }));

http.createServer(function (request, response) {
    let url = request.url;
    if (url == '/')
        url = '/index.html';

    let contentType = {
        '.js': 'text/javascript',
        '.css': 'text/css',
        '.json': 'application/json',
    }[require('path').extname(url)] || 'text/html';

    let chunks = url.split('/').filter(x => x);

    if (chunks[0] == 'list-hir-items'){
        let json = JSON.stringify(
            getFiles(CRATE_ROOT)
                .filter(x =>
                    x.endsWith('thir_export.json')
                        && x.startsWith(CRATE_ROOT)
                ).map(x => x.slice(CRATE_ROOT.length))
        );
        response.writeHead(200, { 'Content-Type': 'application/json' });
        response.end(json, 'utf-8');
    }
    
    let path = chunks[0] == 'crate-sources'
        ? `${CRATE_ROOT}/${chunks.slice(1).join('/')}`
        : `${APP_ROOT}/${chunks.join('/')}`;

    fs.readFile(path, (error, content) => {
        if (error){
            response.writeHead(404);
            response.end('Could not find file '+path, 'utf-8');
        }
        else {
            response.writeHead(200, { 'Content-Type': contentType });
            response.end(content, 'utf-8');
        }
    });
}).listen(PORT);
console.log(`Server running at http://127.0.0.1:${PORT}/
APP_ROOT   = "${APP_ROOT}"
CRATE_ROOT = "${CRATE_ROOT}"`);
