/*
  This webapp is written in vanilla JS as two pure components: `json` and `phases_viewer`.
  */

// Make a DOM node
let mk = (kind, body = [], classes = []) => {
    let e = document.createElement(kind);
    classes.forEach(cl => e.classList.add(cl));
    if (typeof body == 'string') {
        e.innerText = body;
    } else if (body instanceof Array) {
        body.forEach(sub => e.appendChild(sub));
    } else if (body instanceof HTMLElement) {
        e.appendChild(body);
    } else {
        console.error('wrong type for body', body);
    }
    return e;
};

function findNode(o, search){
    let h = o => o instanceof Object ? (search(o) ? o : Object.values(o).map(h).find(x => x)) : null;
    return h(o);
}
let is_span = o => o instanceof Object && "data" in o && "id" in o;

let spanned = span_id => o  => Object.values(o).some(o => is_span(o) && o["id"] === span_id);

let rewrite = f => o => f(
    o instanceof Array
        ? o.map(rewrite(f))
        : (o instanceof Object ? Object.fromEntries(Object.entries(o).map(([k, v]) => [k, rewrite(f)(v)])) : o)
);
let loc_to_string = ({col, line}) => `${line}:${col}`;
let filename_to_string = name =>
    ((name instanceof Array && name[0] == 'Real' && name[1]?.[0] =='LocalPath') ?
     name?.[1]?.[1] : null) || JSON.stringify(name);
let span_data_to_string = ({filename, lo, hi}) => `<${filename_to_string(filename)} ${loc_to_string(lo)}→${loc_to_string(hi)}>`;
let span_to_string = ({id, data}) => data.length ? data.map(span_data_to_string).join('∪') : '<dummy>';
let clean = rewrite(o => {
    if(!(o instanceof Object))
        return o;
    if (is_span(o))
        return span_to_string(o);
    return o;
});

function json(json) {
    let o = JSON.parse(JSON.stringify(json));
    let root = mk('div', [], ['json-viewer']);
    let state = {
        open: new Map(),
        default_open: false,
    };
    function render_all() {
        root.replaceChildren(render(o, []));
        let expand_button = mk('button', state.default_open ? '🡒🡐' : '🡘', ['expand-all']);
        expand_button.style = `
            position: absolute;
            top: 1px;
            right: 1px;
            padding: 0 3px;
            margin: 0;
            line-height: 0;
            height: 16px;
        `;
        expand_button.onclick = () => {
            state.default_open = !state.default_open;
            render_all();
        };
        root.prepend(expand_button);
    }
    let key_of_path = path => JSON.stringify(path);
    let set_open = (path, v) => state.open.set(key_of_path(path), v);
    let is_open = (path, def = path.length < 6) => {
        let b = state.open.get(key_of_path(path));
        return b === undefined ? (state.default_open || def) : b;
    };
    let swap = (path, def) => {
        set_open(path, !is_open(path, def), false);
        render_all();
    };
    let is_constructor = o => {
        if (o instanceof Array && (o.length == 2 || o.length == 1)) {
            let [constructor, arg] = o;
            if(typeof constructor == 'string' && constructor[0] == constructor[0].toUpperCase()) {
                return true;
            }
        }
        return false;
    };
    let is_simple = o => {
        if (o instanceof Object) {
            if (is_constructor(o)) {
                return o[1] === undefined;
            }
            return false;
        }
        return true;
    };
    function render(o, path, add_comma = true) {
        function as_code(o) {
            let code = mk('code');
            code.innerHTML = Prism.highlight(JSON.stringify(o, null, 4), Prism.languages.json, 'json');
            return add_comma ? mk('span', [code, mk('span', ',')]) : code;
        }
        if (o instanceof Object) {
            if (is_constructor(o)) {
                
                let [constructor, arg] = o;
                let cdiv = mk('span', constructor + (arg === undefined ? '' : ' '), ['constructor']);
                if (constructor == "Concrete" && "crate" in arg && "path" in arg) {
                    let {crate, path} = arg;
                    return mk('span', [
                        ...[crate, ...path].map((chunk, i) => [...(i > 0 ? [mk('span', '::', ['pathsep'])] : []), mk('span', chunk, ['pathchunk'])]).flat(),
                        add_comma ? [mk('span', ',')] : []
                    ].flat());
                }
                let contents = arg === undefined ? [] : render(arg, path, false);
                if(arg !== undefined && is_constructor(arg))
                    contents = mk('span', [mk('span', '('), contents, mk('span', ')')]);
                
                let self_path = [...path, []];
                let elide = mk('span', '…');
                elide.onclick = () => swap(self_path);
                let open = arg === undefined || is_open(self_path);
                cdiv.onclick = () => swap(self_path);
                return mk('span', [
                    cdiv,
                    open ? contents : elide,
                    add_comma ? [mk('span', ',')] : []
                ].flat());
            }
            if (o instanceof Array) {
                let self_path = [...path, []];
                let open = is_open(self_path);
                let bracket = mk('code', '[');
                bracket.onclick = () => swap(self_path);
                let elide = mk('span', '…');
                elide.onclick = () => swap(self_path);
                return mk('span', [
                    bracket,
                    open ? mk('ul', o.map((v, i) => {
                        let new_path = [...path, i];
                        let simple_val = is_simple(v);
                        let open = simple_val || is_open(new_path);
                        return [mk('li', render(v, new_path), ['v'])];
                    }).flat()) : elide,
                    mk('code', ']'),
                    ...(add_comma ? [mk('span', ',')] : [])
                ]);
            }
            
            return mk('span', [
                mk('code', '{'),
                mk('ul', Object.entries(o).map(([k, v]) => {
                    let new_path = [...path, k];
                    let simple_val = is_simple(v);
                    let open = simple_val || is_open(new_path);
                    let elide = mk('span', '…');
                    elide.onclick = () => swap(new_path, open);
                    let contents = mk((simple_val || !open) ? 'span' : 'span', open ? render(v, new_path) : [elide, mk('span', ',')], ['v']);
                    let key = mk('span', [
                        mk('span', k+': '),
                    ].flat(), ['k']);
                    key.onclick = () => swap(new_path);
                    return [mk('li', [
                        key,
                        contents
                    ], ['p'])];
                }).flat(), ['o']),
                mk('code', '}'),
                ...(add_comma ? [mk('span', ',')] : [])
            ]);
        } else if (typeof o == "string" && o.length > 20) {
            let new_path = [...path, 'v'];
            let code = as_code(is_open(new_path, false) ? o : o.slice(0, 20)+'…');
            code.onclick = () => swap(new_path, false);
            return code;
        } else {
            return as_code(o);
        }
    };
    render_all();
    return root;
}

const SEED = Date.now();
async function phases_viewer(state = {index: 0, ast_focus: null, seed: SEED}) {
    let data = await (await fetch('debug-hax-engine.json?seed='+state.seed)).json();
    if (!data[state.index] && state.index != 0) {
        return phases_viewer({...state, index: 0});
    };
    let current = null;
    let s = '';
    let header = mk('header');
    for(let i in data) {
        let o = data[i];
        let w = 100;
        let active = state.index == i;
        let self = mk('div', o.name.toLowerCase().replace(/reject_not_in_/g, 'rej ~').replace(/_/g, ' '), ['header', active ? 'active' : 'inactive']);
        self.style = `width: ${w}px; font-variant: small-caps;
                      position: relative; top: ${w}px; left: 10px;
                      transform-origin: 0% 50%; transform: rotate(-40deg);
                      color: ${active ? 'black' : 'gray'}; user-select: none;`;
        self.onclick = () => phases_viewer({...state, index: i, ast_focus: null});
        let container = mk('div', self, []);
        container.style = `display: inline-block; width: 18px; height: ${w}px;`;
        if(active){
            current = o;
        }
        header.appendChild(container);
    }
    let last_item = null;
    let codes = [current.rustish].map(({string, map}) => {
        let src = string;
        let code = mk('code', [], ['language-rust']);
        code.innerHTML = Prism.highlight(src, Prism.languages.rust, 'rust');

        [...code.childNodes]
            .filter(o => o.nodeType === Node.TEXT_NODE)
            .forEach(o => {
                let n = mk('span');
                n.textContent = o.textContent;
                code.replaceChild(n, o);
            });

        let mappings = map.slice(0).reverse();
        let stack = [...code.childNodes].reverse();

        let highlighted = null;
        let maybe = [];
        
        while(stack.length) {
            let node = stack.pop();
            let [len, id, s] = mappings.pop();
            let text = node.textContent;
            if (len > text.length) {
                mappings.push([len - text.length, id, s.slice(text.length)]);
            } else if (len < text.length) {
                let after = node.cloneNode();
                let left = text.slice(0, len);
                let right = text.slice(len);
                src = right + src;
                after.textContent = right;
                node.textContent = left;
                node.after(after);
                stack.push(after);
            }
            let active = state.ast_focus === id && text.trim();
            node.onclick = ev => {
                phases_viewer({...state, ast_focus: id});
                ev.stopPropagation();
            };
            if (active) {
                highlighted = highlighted || [];
                highlighted.push(...maybe);
                maybe = [];
                active && node.classList.add('active');
                last_item = node;
            } else if (highlighted) {
                maybe.push(node);
            }
        }

        (highlighted||[]).map(o => o.classList.add('in-range'));
        
        return code;
    });
    let pre = mk('pre', codes);
    let main = mk('main', [header, pre]);
    if(last_item) {
        let ast = clean(findNode(current.items, spanned(state.ast_focus)));
        let dialog = mk('dialog', json(ast));
        dialog.setAttribute('open', true);
        dialog.onclick = ev => {
            ev.stopPropagation();
        };
        main.onclick = ev => phases_viewer({...state, ast_focus: null});
        last_item.after(dialog);
    }
    let app_root = document.querySelector('#app');
    app_root.childNodes.forEach(old => old.remove());
    app_root.appendChild(main);
    document.body.onkeydown = (e) => {
        let key = ({'ArrowRight': 'n', 'ArrowLeft': 'p'})[e.key] || e.key;
        (({
            'n': () => phases_viewer({...state, index: state.index + 1, ast_focus: null}),
            'p': () => phases_viewer({...state, index: state.index ? state.index - 1 : data.length - 1, ast_focus: null}),
            'r': () => phases_viewer({...state, seed: Date.now(), ast_focus: null}),
        })[key] || Function)();
    };
}
phases_viewer();
