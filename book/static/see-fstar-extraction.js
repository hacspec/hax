function installButtons() {
    let id = 0;
    for(let fst of document.querySelectorAll('pre + pre')) {
        let parent = fst.parentElement;
        let rust = fst.previousElementSibling;
        let w = s => `<div class=snippet>${s}</div>`;
        let both = w(rust.outerHTML) + w(fst.outerHTML);
        parent.removeChild(rust);
        let snippets = document.createElement('div');
        snippets.classList.add('snippets');
        snippets.innerHTML = both;
        let buttons = document.createElement('div');
        id++;
        buttons.classList.add('buttons');
        buttons.innerHTML  = `<button>Rust</button><button>F* extraction</button>`;
        let mk_active = i => {
            [snippets, buttons].map(el => 
                [...el.children].map((x, j) => {
                    x.classList[j==i ? 'remove' : 'add']('fstar-rust-snippet-hidden');
                    x.classList[j==i ? 'add' : 'remove']('fstar-rust-snippet-active');
                })
            );
        };
        [...buttons.children].map((child, nth) =>
            (child.onclick = _ => mk_active(nth))
        );
        const RUST = 0;
        mk_active(RUST);
        
        let wrapper = document.createElement('div');
        wrapper.classList.add('rust-fstar-wrapper');
        wrapper.appendChild(buttons);
        wrapper.appendChild(snippets);
        parent.replaceChild(wrapper, fst);
    }
};

window.addEventListener("load", installButtons);
