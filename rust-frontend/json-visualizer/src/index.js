import React from 'react';
import ReactDOM from 'react-dom/client';
import { JsonViewer } from '@textea/json-viewer';

import { Code, CodeBlock, monokai, github, nord } from "react-code-blocks";
import './index.css';

let theme = nord;

function takeAround(lines, lo, hi) {
    let diff = hi - lo;
    let context = 2;
    let startingLineNumber = Math.max(0, lo - context);
    let text = lines.slice(startingLineNumber).slice(0, diff + 1 + context).join('\n');
    return { text, startingLineNumber, highlight: `${lo - startingLineNumber}-${hi - startingLineNumber}` };
}

let is_span_virtual = v =>
    v?.lo?.col === 0 && v?.hi?.col === 0 && v?.lo?.line === 1 && v?.hi?.line === 1;

let clean = o => {
    if (o instanceof Array) {
        return o
            .filter(o =>
                !(
                    is_span_virtual(o?.ident?.span)
                        && is_span_virtual(o?.span)
                ) &&
                    true
                // o?.span?.lo?.line == 1 &&
                //     o?.span?.hi?.line == 1 &&
                //     o?.span?.lo?.col == 0 &&
                //     o?.span?.hi?.col == 0 &&
                // o?.ident?.id !== 0 &&
                // o?.ident?.name !== "std"
            )
            .map(clean);
    }
    if (o instanceof Object) {
        delete o["vis_span"];
        return Object.fromEntries(Object.entries(o).map(([k, v]) => [k, clean(v)]));
    } else {
        return o;
    }
}

async function main(){
    let getSource = (() => {
        let cache = {};
        let cache_promises = {};
        return async (path, setter) => {
            if(cache[path])
                setter(cache[path]);
            else {
                if (!cache_promises[path]){
                    console.log('Fetching '+path);
                    cache_promises[path] = (async () => await (await fetch('/crate-sources/'+path)).text())();
                }
                let str = await cache_promises[path];
                cache[path] = {
                    lines: str.split('\n'),
                    str
                };
                setter(cache[path]);
            }
        };
    })();

    let Span = (value) => {        
        let key = value.path.slice(-1);
        let path = value.value?.filename?.Real?.LocalPath;
        let lo = value.value?.lo;
        let hi = value.value?.hi;
        let [state, setState] = React.useState(0);
        let [contents, setContents] = React.useState(null);
        React.useEffect(() => {
            if (path)
                getSource(path, setContents);
        }, [path]);
        if (path) {
            if(contents === null){
                return (<i style={{color: '#9b59b6', fontSize: '50%'}}>{"[loading...]"}</i>);
            }
            if (is_span_virtual(value.value)) {
                return (<i style={{color: '#9b59b6', fontSize: '50%'}}>{"[virtual]"}</i>);
            }
            if (lo.line == hi.line && lo.col == hi.col)
                return (<i style={{color: '#9b59b6', fontSize: '50%'}}>{"[empty range]"}</i>);
            return (<div style={{
                             display: state ? 'inline-block' : 'inline-block',
                             verticalAlign: 'middle'
                         }} className="user-selection"
                         onClick={() => state <= 1 && window.getSelection().type != "Range" && setState(+!state)}
                    >
                        {({
                            0: <>
                                   <Code
                                       text={
                                           lo.line == hi.line
                                               ? contents.lines[lo.line-1]?.slice(lo.col, hi.col)
                                               : contents.lines[lo.line-1]?.slice(lo.col)
                                       }
                                       language={"rust"}
                                       theme={theme}
                                   />
                                   {lo.line != hi.line ?
                                    <>
                                        <span style={{display: 'inline-block', padding: '1px', paddingRight: '4px', position: 'relative', top: '-3px', letterSpacing: '-3px'}}>{'...'}</span>
                                        <Code
                                            text={
                                                contents.lines[hi.line-1]?.slice(0, hi.col)
                                            }
                                            language={"rust"}
                                            theme={theme}
                                        />
                                    </>
                                    : (<></>)}
                               </>,
                            1: <>
                                   <CodeBlock
                                       {...takeAround(contents.lines, lo.line, hi.line)}
                                       language={"rust"}
                                       theme={theme}
                                   />
                                   <button style={{fontSize: '60%', marginTop: '2px'}} onClick={e => {
                                               setState(2);
                                               e.stopPropagation()
                                           }}>View full JSON</button>
                               </>,
                            2: <>
                                   <JsonViewer value={value.value}/>
                                   <button style={{fontSize: '60%', marginTop: '2px'}} onClick={e => {
                                               setState(0);
                                               e.stopPropagation()
                                           }}>Reduce</button>
                               </>
                        })[state] || <b>ERR</b>}
                        {/* <i>{JSON.stringify(value.value)}</i> */} 
                    </div>);
        } else {
            return <b>{JSON.stringify(value.value)}</b>;
        }
    };

    let ShowJson = ({json_file}) => {
        const [data, setData] = React.useState(null);
        
        React.useEffect(() => {
            (async () => {
                try {
                    setData(clean(await (await fetch('/crate-sources/' + json_file)).json()));
                } catch {
                    setData({error: `Could not fetch file`, path: json_file});
                }
            })()
        }, [json_file]);

        return data ?
            (<JsonViewer
                 value={data}
                 valueTypes={[
                     {
                         is: (value) => value instanceof Object
                             && "lo" in value && "hi" in value,
                            Component: Span
                     }
                 ]}
             />) : <span>Loading...</span>;
    };
    
    let App = () => {
        let [suggestions, setSuggestions] = React.useState([]);
        let [file, setFile] = React.useState(null);
        let [field, setField] = React.useState('');
        
        React.useEffect(() => {
            let f = async () => {
                try {
                    let items = await (await fetch("list-hir-items")).json();
                    setSuggestions(items);
                    if(items.length == 1)
                        setFile(items[0]);
                } catch {
                    // hack to get that working without custom server
                    setFile('hir-items.json');
                }
            };
            f();
        }, []);
        
        return file ? (
            <>
                <button onClick={() => setFile(null)}>View another file</button>
                <ShowJson json_file={file}/>
            </>
        ) : (
            <>
                <input
                    onChange={e => setField(e.target.value)}
                    onKeyDown={e => e.key == 'Enter' && setFile(field)}
                    value={field}
                    list="files"
                />
                <datalist id="files">
                    {
                        suggestions.map((s, key) => <option key={key} value={s}></option>)
                    }
                </datalist>
                <button onClick={e => setFile(field)}>load</button>
            </>
        );
    };
    
    const root = ReactDOM.createRoot(document.getElementById('root'));
    root.render(
            <React.StrictMode>
            <App />
            </React.StrictMode>
    );
}
main();

                    
