// Call into the API of the hax playground
function call_playground(result_block, query, text) {
    let raw_query = async (API_URL, hax_version, query, files, on_line_received) => {
        let response = await fetch(`${API_URL}/query/${hax_version}/${query}`, {
            method: "POST",
            headers: {
                'Accept': 'application/json',
                'Content-Type': 'application/json'
            },
            body: JSON.stringify(files),
        });

        let decoder = new TextDecoder();
        let leftover = "";
        let reader = response.body.getReader();
        while (true) {
            const { done, value } = await reader.read();
            if (done) break;
            leftover += decoder.decode(value);
            let lines = leftover.split('\n');
            let entire_lines = lines.slice(0, -1);
            leftover = lines.slice(-1)[0];
            for (const line of entire_lines)
                on_line_received(line);
        }
    };
    let hax_version = '5ca1c13023200dee0cca6237901a3b5a69ad345a';
    let playground_url = 'https://hax-playground.cryspen.com';
    let ansi_up = new AnsiUp();
    let first = true;
    let logs = document.createElement('div');
    logs.style = 'font-size: 80%; background: #00000010; padding: 3px;';
    raw_query(
        playground_url,
        hax_version,
        query,
        [['src/lib.rs', text]],
        x => {
            if (first) {
                result_block.style.padding = '0.7em 1.2em';
                result_block.innerText = "";
                result_block.appendChild(logs);
            }
            first = false;
            let json = {};
            try {
                json = JSON.parse(x);
            } catch (_) { }
            if (json.Stderr || json.Stdout) {
                logs.innerHTML += '<div>' + ansi_up.ansi_to_html(json.Stderr || json.Stdout) + "</div>";
            }
            if (json.Done) {
                let out = [];
                for (let file in json.Done.files) {
                    if (file.endsWith('.rs'))
                        continue;
                    let contents = json.Done.files[file];
                    contents = contents.split('open FStar.Mul')[1].trim();
                    contents = contents.replace(/$/gm, ' ').trim();
                    out.push([file, contents]);
                }
                if (json.Done.success)
                    result_block.innerText = "";
                else
                    result_block.innerHTML += "<br/>";
                let result = document.createElement('div');
                if (out.length == 1) {
                    result.innerText = out[0][1];
                } else {
                    result.innerText = out.map(([file, s]) => '(* File: ' + file + ' *) \n' + s).join('\n\n').trim();
                }
                result_block.appendChild(result);
                if (json.Done.success && query.includes('+tc')) {
                    result_block.innerHTML += '<div style="float: left; padding: 3px; padding-top: 8px; position: relative; top: 6px;"><span style="color: gray;">Status: </span><span style="color: green">✓ F* successfully typechecked!</span></div>';
                }
                hljs.highlightBlock(result);
                result_block.innerHTML += `<br/><a style="float:right; font-family: 'Open Sans', sans-serif; font-size: 70%; cursor: pointer; color: gray; text-transform: uppercase; position: relative; top: -10px;" href='${playground_url}/#fstar/${hax_version}/${LZString.compressToEncodedURIComponent(text)}'>Open in hax playground ↗</a>`;
            }
        },
    );
}

function setup() {
    for (let e of document.querySelectorAll('pre')) {
        let code = e.querySelector("code");
        let lines = [
            ...code.children
        ].map(line => line.innerText.replace(/^\n+/, '').replace(/\n+$/, ''))
            .join("\n").trim().split('\n');
        let contents = lines.filter(line => !line.startsWith('# ')).join('\n');
        let w = e.parentElement;
        if (!w.classList.contains("playable"))
            continue;

        code.innerHTML = "<pre></pre>";
        let inner = code.children[0];
        inner.style.backgroundColor = "transparent";

        let editor = ace.edit(inner);
        editor.setValue(contents, -1);
        editor.setValue(contents, 1);
        editor.getSession().setMode("ace/mode/rust");
        editor.setOptions({
            maxLines: Infinity,
            showGutter: false,
            fontSize: "1em",
            highlightActiveLine: false,
        });

        let result_block = document.createElement("pre");
        result_block.style.fontFamily = '"Monaco", "Menlo", "Ubuntu Mono", "Consolas", "Source Code Pro", "source-code-pro", monospace';
        result_block.style.fontSize = '0.85em';
        result_block.style.background = '#f3f3f3';
        w.append(result_block);

        let header = lines.filter(line => line.startsWith('# ')).map(line => line.slice(2)).join('\n');
        let getCode = () => header + '\n' + editor.getValue();

        let button_translate = document.createElement("button");
        button_translate.innerHTML = `<i class="fa-solid fa-play"></i>`;
        button_translate.classList.add('md-icon');
        button_translate.classList.add('md-clipboard');
        button_translate.classList.add('md-hax-playground');
        button_translate.style.right = "2.4em";
        button_translate.onclick = () => {
            call_playground(result_block, 'fstar', getCode());
        };
        e.prepend(button_translate);


        let button_tc = document.createElement("button");
        button_tc.innerHTML = `<i class="fa-solid fa-check"></i>`;
        button_tc.classList.add('md-icon');
        button_tc.classList.add('md-clipboard');
        button_tc.classList.add('md-hax-playground');
        button_tc.style.right = "4.5em";
        button_tc.onclick = () => {
            call_playground(result_block, 'fstar+tc', getCode());
        };
        e.prepend(button_tc);

        code.style.padding = "0 0.9em";
    }
}

setup();
