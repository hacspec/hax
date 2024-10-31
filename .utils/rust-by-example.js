// This script expect Rust By Example to be in current directory

const fs = require('fs');
const SRC_DIR = 'src';

// Lists all markdown files under `SRC_DIR`
function getMarkdownFiles() {
    return fs.readdirSync(SRC_DIR, { recursive: true })
        .filter(path => path.endsWith('.md'));
}

// Code blocks from a file of given path
function extractCodeBlocks(path) {
    let contents = fs.readFileSync(SRC_DIR + '/' + path).toString();
    let blocks = contents
        .split(/^```/m)
        .filter((_, i) => i % 2 == 1)
        .map(s => {
            let lines = s.split('\n');
            let modifiers = lines[0].split(',').map(x => x.trim()).filter(x => x);
            let contents = lines.slice(1).join('\n');
            return {modifiers, contents};
        })
        .filter(x => x.modifiers.includes('rust'));
    let name = path.replace(/[.]md$/, '').split('/').join('_');
    return {name, blocks};
}

let code = getMarkdownFiles()
    .map(extractCodeBlocks)
    .filter(({blocks}) => blocks.length);

// Strips the comments of a rust snippet
let stripComments = rust_snippet => rust_snippet.replace(/[/][/]+.*/mg, '');

// Given a Rust snippet, returns `true` whenever we detect a top-level
// `let` binding: this means we need to wrap the snippet in a function.
let isDirectLet = rust_snippet => stripComments(rust_snippet).trim().startsWith('let ');

// Wraps a Rust snippet inside a function
let protectSnippet = rust_snippet => `fn wrapper_fn() { let _ = {${rust_snippet}}; }`;

function codeBlocksToModules(code_blocks) {
    let denylist = [
        /unsafe_asm \d+/
    ];
    let modules = {};
    
    for(let {name, blocks} of code_blocks) {
        let mod_section = `section_${name}`;
        modules[mod_section] = {};
        let nth = 0;
        for(let {modifiers, contents} of blocks) {
            nth += 1;
            if(['edition2015', 'compile_fail', 'ignore'].some(m => modifiers.includes(m))) {
                continue;
            }
            let id = `section_${name} ${nth}`;
            // Remove top-level assertions
            contents = contents.replace(/^# assert.*\n?/mg, '');
            // Strip `# ` (the mdbook marker to hide a line)
            contents = contents.replace(/^# /mg, '');
            // Whenever we detect a `let`
            if(isDirectLet(contents))
                contents = protectSnippet(contents);
            if(denylist.some(re => id.match(re)))
                continue;
            let mod_snippet = `snippet_${nth}`;
            // Replace `crate::` by a full path to the current module
            contents = contents.replace(/crate::/g, 'crate::' + mod_section + '::' + mod_snippet + '::');
            modules[mod_section][mod_snippet] = `// modifiers: ${modifiers.join(', ')}\n` + contents;
        }
    }

    return modules;
}

let modules = codeBlocksToModules(code);

let OUTPUT_CRATE = 'rust-by-examples-crate';
fs.rmSync(OUTPUT_CRATE, { recursive: true, force: true });
fs.mkdirSync(OUTPUT_CRATE, { recursive: true });
const { execSync } = require('child_process');
execSync("cargo init --lib", { cwd: OUTPUT_CRATE });

let OUTPUT_CRATE_SRC = OUTPUT_CRATE + '/src/';
fs.rmSync(OUTPUT_CRATE_SRC, { recursive: true, force: true });
let root_mod = '#![allow(unused)]';
for(let mod_name in modules) {
    let submodules = modules[mod_name];
    fs.mkdirSync(OUTPUT_CRATE_SRC + mod_name, { recursive: true });
    let mod_contents = '';
    for (let submod_name in submodules) {
        let contents = submodules[submod_name];
        fs.writeFileSync(OUTPUT_CRATE_SRC + mod_name + '/' + submod_name + '.rs', contents);
        mod_contents += 'pub mod ' + submod_name + ';\n';
    }
fs.writeFileSync(OUTPUT_CRATE_SRC + mod_name + '.rs', mod_contents);
    root_mod += 'pub mod ' + mod_name + ';\n';
}
fs.writeFileSync(OUTPUT_CRATE_SRC + '/lib.rs', root_mod);


// A list of [<module_name>, [<snippet_number>]] that are known not to be processed by hax
let cargo_hax_denylist = [
    ['error_iter_result', [3]],
    ['error_option_unwrap_defaults', [3,4]],
    ['flow_control_for', [1,2,3,5]],
    ['flow_control_if_let', [3]],
    ['flow_control_loop_nested', [1]],
    ['flow_control_loop_return', [1]],
    ['flow_control_loop', [1]],
    ['flow_control_match_binding', [1,2]],
    ['flow_control_match_destructuring_destructure_pointers', [1]],
    ['flow_control_match_destructuring_destructure_slice', [1]],
    ['flow_control_match', [1]],
    ['flow_control_while_let', [1,2]],
    ['fn_closures_capture', [1]],
    ['fn_closures_input_parameters', [1]],
    ['fn', [1]],
    ['hello_print_fmt', [1]],
    ['macros_dry', [1]],
    ['scope_borrow_alias', [1]],
    ['scope_borrow_ref', [1]],
    ['scope_move_mut', [1]],
    ['scope_raii', [1]],
    ['std_arc', [1]],
    ['std_hash', [1]],
    ['std_misc_arg_matching', [1]],
    ['std_misc_channels', [1]],
    ['std_misc_file_read_lines', [3]],
    ['std_misc_threads', [1]],
    ['std_misc_threads_testcase_mapreduce', [1]],
    ['std_str', [1]],
    ['trait_iter', [1]],
    ['trait', [1]],
    ['unsafe', [1,2]],
].map(([module, snippets]) => snippets.map(n => `section_${module}::snippet_${n}`)).flat();

let include_clause = cargo_hax_denylist.map(path => `-*::${path}::**`).join(' ');

execSync(`cargo hax into -i '${include_clause}' fstar`, { cwd: OUTPUT_CRATE, stdio: 'inherit' });
