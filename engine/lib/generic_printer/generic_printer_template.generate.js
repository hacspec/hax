#!/usr/bin/env node

// This script regenerates `generic_printer_template.ml`

const {readFileSync, writeFileSync} = require('fs');
const {execSync} = require('child_process');

const GENERIC_PRINTER_DIR = `lib/generic_printer`;
const GENERIC_PRINTER = `${GENERIC_PRINTER_DIR}/generic_printer.ml`;
const TEMPLATE = `${GENERIC_PRINTER_DIR}/generic_printer_template.ml`;

// Utility function to format an OCaml module
let fmt = path => execSync(`ocamlformat -i ${path}`);

// Go to the root of the engine
require('process').chdir(`${execSync('git rev-parse --show-toplevel').toString().trim()}/engine`);

// Prints the signature of module `Generic_printer` (using `ocaml-print-intf`)
let mli = execSync(`dune exec -- ocaml-print-intf ${GENERIC_PRINTER}`).toString();

// Parses all 
let virtual_methods = [...mli.matchAll(/^( +)method (private )?virtual +(?<name>.*) +:(?<sig>.*(\n \1.*)*)/gm)];

let output = [];
for(let v of virtual_methods) {
    let {name, sig} = v.groups;
    let out = sig.trim().split('->').slice(-1)[0].trim().split('.').slice(-1)[0];
    let args = sig.trim().split('->').map((s, i) => {
        let chunks = s.trim().split(':').reverse();
        if(chunks.length > 2 || chunks.length == 0) {
            throw "Chunks: bad length";
        }
        let [type, name] = chunks;
        name = name ? '~'+name+':_' : '_x'+(i + 1);
        return {type, name};
    }).map(n => n.name).slice(0, -1).join(' ');
    
    output.push(`method ${name} ${args} = default_${out}_for "${name}"`);
}

{
    let [before, _, after] = readFileSync(TEMPLATE).toString().split(/(?=\(\* (?:BEGIN|END) GENERATED \*\))/);
    writeFileSync(TEMPLATE, before + '\n(* BEGIN GENERATED *)\n' + output.join('\n') + '\n' + after);
}

fmt(TEMPLATE);
