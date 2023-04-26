const keys = p => 
    new Set(
        Object.keys(p)
            .filter(k => ![
                'description', 'maxItems', 'minItems'
            ].includes(k))
            .filter(k => p?.additionalProperties !== false || k != 'additionalProperties')
    );
const eq = (xs, ys) =>
      xs.size === ys.size &&
      [...xs].every((x) => ys.has(x));

let todo = (todo = "todo") => null;

let assert = (fact, msg = "assert") => {
    if(!fact)
        throw msg;
};

let exact_keys = (o, ...key_list) => {
    // console.log('exact_keys', o);
    // console.log('keys=', keys(o));
    // console.log('agaisnt=', new Set(key_list));
    return eq(keys(o), new Set(key_list));
};


const clean = o => {
    if (o instanceof Object
        && exact_keys(o, 'allOf')
        && o.allOf.length == 1
       ) {
        let first = o.allOf[0];
        delete o['allOf'];
        for (let k in first)
            o[k] = first[k];
    }
    if (o instanceof Object
        && 'type' in o
        && o.type instanceof Array
        && o.type.length === 2
        && o.type.includes('null')
       ) {
        let type = o.type.filter(x => x != 'null')[0];
        let other = JSON.parse(JSON.stringify(o));
        other.type = type;
        for (let k in o)
            delete o[k];
        o.anyOf = [other, {type: 'null'}];
    }
    if (o instanceof Array) {
        return o
            .filter(o => true)
            .map(clean);
    }
    if (o instanceof Object) {
        delete o['maxItems'];
        delete o['minItems'];
        return Object.fromEntries(Object.entries(o).map(([k, v]) => [k, clean(v)]));
    } else {
        return o;
    }
};
let isUpperCase = s => s.toUpperCase() == s;
let startsWithUpper = s => isUpperCase(s[0]);

let makeFirstCharUpper = s => s[0].toUpperCase() + s.slice(1);
let makeFirstCharLower = s => s[0].toLowerCase() + s.slice(1);


let variantNameOf = s => {
    let v = makeFirstCharUpper(s);
    if (['Some', 'None'].includes(v))
        return v + "'";
    return v;
};
let typeNameOf = s => s.replace(/[A-Z]/g, (l, i) => `${i?'_':''}${l.toLowerCase()}`);
let fieldNameOf = s => {
    if (['then', 'if', 'end', 'open', 'include', 'begin', 'fun', 'initializer'].includes(s))
        return s + "'";
    return s;
};

let ensureUnique = (() => {
    let cache = {};
    return (kind, v, disambiguer) => {
        let key = JSON.stringify({kind, v});
        // TODO: enble check below, find a good solution
        // if(cache[key])
        //     throw `dup ${kind}, ${v}`;
        cache[key] = true;
        return v;
    };
})();

const util = require('util');
let log_full = o => console.error(util.inspect(o, {showHidden: false, depth: null, colors: true}));

let trace1 = (name, f) => (input) => {
    let output = f(input);
    log_full({name, input, output});
    return output;
};

let ocaml_of_type_expr = (o, path) => {
    if (!path)
        throw "Path missing!";
    let {kind, payload} = o;
    return (({
        option: type => `(${ocaml_of_type_expr(type, [...path, 'option'])} option)`,
        tuple: types => `(${types.map((t, i) => ocaml_of_type_expr(t, [...path, 'tuple', i])).join(' * ')})`,
        array: type => `(${ocaml_of_type_expr(type, [...path, 'array'])} list)`,
        boolean: _ => `bool`,
        string: _ => `string`,
        char: _ => `char`,
        integer: _ => o.bigint ? `string` : `int`,
        name: payload => typeNameOf(payload),
        // name: payload => payload,
    })[kind] || (_ => {
        log_full(o);
        throw "ocaml_of_type_expr: bad kind "+kind;
    }))(payload);
};


let mk_match = (scrut, arms, path) => {
    if(!path){
        console.trace();
        throw "Path missing!";
    }
    // console.log({scrut, arms});
    return `
begin match ${scrut} with
${[...arms, ['_', `failwith ("parsing error: ${path} LINE=" ^ string_of_int __LINE__ ^ " JSON=" ^ Yojson.Safe.pretty_to_string ${scrut})`]].map(([pat, expr]) => `${pat} -> ${expr}`).join('\n|')}
end
`;
};

let wrap_paren = s => `(${s})`;

let ocaml_yojson_of_type_expr = (o, subject, path) => {
    if (!path)
        throw "Path missing!";
    let {kind, payload} = o;
    return `(${(({
        option: type => `match ${subject} with | Option.Some x -> ${ocaml_yojson_of_type_expr(type, 'x', [...path, 'Some'])} | _ -> \`Null`,
        tuple: types =>
            `let (${types.map((t, i) => 'x' + i)}) = ${subject} in \`List [${types.map((t, i) => ocaml_yojson_of_type_expr(t, 'x' + i, [...path, 'tuple', i])).join(';')}]`,
        array: type => 
            `\`List (List.map (fun x -> ${ocaml_yojson_of_type_expr(type, 'x', [...path, 'array'])}) ${subject})`,
        boolean: _ => `\`Bool ${subject}`,
        string: _ => `\`String ${subject}`,
        integer: _ => `\`${o.bigint ? 'Intlit' : 'Int'} ${subject}`,
        char: _ => `\`String (Base.Char.to_string ${subject})`,
        name: payload => `to_json_${typeNameOf(payload)} ${subject}`,
    })[kind] || (_ => {
        log_full(o);
        throw "ocaml_arms_of_type_expr: bad kind "+kind;
    }))(payload)})`;
};


let ocaml_arms_of_type_expr = (o, path) => {
    if (!path)
        throw "Path missing!";
    let {kind, payload} = o;
    return (({
        option: type => [
            [`\`Null`, `Option.None`],
            ...ocaml_arms_of_type_expr(type, [...path, 'option']).map(([pat, expr]) => [pat, `Option.Some (${expr})`])
        ],
        tuple: types => {
            let sub_matches = types.map((type, i) => 
                mk_match(`v${i}`, ocaml_arms_of_type_expr(type, [...path, 'tuple', i]), [...path, 'tuple']));
            return [
                [`\`List [${types.map((_, i) => `v${i}`).join(';')}]`,
                 `(${sub_matches.join(',')})`
                ],
            ];
        },
        array: type => [
            [`\`List l`,
             `List.map (fun x -> ${mk_match('x', ocaml_arms_of_type_expr(type, [...path, 'array']), [...path, 'array'])}) l`
            ]
        ],
        boolean: _ => [[`\`Bool b`, 'b']],
        string: _ => [[`\`String s`, 's']],
        char: _ => [[`\`String s`, 'String.get s 0']],
        integer: _ => o.bigint ?
            [
                [`\`Int i`, 'string_of_int i'],
                [`\`Intlit s`, 's']
            ] : [
                [`\`Int i`, 'i'],
                [`\`Intlit lit`, 'failwith "Got big number, while a int was expected"']
            ]
        ,
        name: payload => [['remains', `parse_${typeNameOf(payload)} remains`]],
    })[kind] || (_ => {
        log_full(o);
        throw "ocaml_arms_of_type_expr: bad kind "+kind;
    }))(payload);
};

let parse_type_name = s => {
    if (!s.startsWith('#/definitions/'))
        throw s;
    return s.split('/').slice(-1)[0];
};


let is_type = {
    option: def => {
        if (exact_keys(def, 'anyOf')
            && def.anyOf.length === 2
            && is_type.expr(def.anyOf[0])
            && exact_keys(def.anyOf[1], 'type')
            && def.anyOf[1].type === 'null'
           )
            return {
                kind: 'option',
                payload: is_type.expr(def.anyOf[0])
            };
        return false;
    },
    
    tuple: def => {
        if (exact_keys(def, 'type', 'items')
            && def.type === 'array'
            && def.items instanceof Array
            && def.items.every(is_type.expr))
            return {
                kind: 'tuple',
                payload: def.items.map(is_type.expr)
            };
        return false;
    },
    
    array: def => {
        if (exact_keys(def, 'type', 'items')
            && def.type === 'array'
            && is_type.expr(def.items))
            return {
                kind: 'array',
                payload: is_type.expr(def.items),
            };
        return false;
    },
    
    expr: def => 
    (exact_keys(def, '$ref') ? {
        kind: 'name', payload: parse_type_name(def['$ref'])
    } : false)
        || is_type.option(def)
        || is_type.array(def)
        || is_type.tuple(def)
        || (def.type === 'integer'
            ? {kind: 'integer', bigint: def.format.endsWith('int128')}
            : false)
        || (def.type === 'string' && def.maxLength === def.minLength && def.minLength === 1
            ? {kind: 'char'}
            : false)
        || ( ( exact_keys(def, 'type')
               && ['boolean', 'string'].includes(def.type)
             ) ? {kind: def.type} : false
           ) || false,

    record: def => {
        if ((eq(keys(def), new Set(["type", "required", "properties"]))
             || eq(keys(def), new Set(["type", "properties"]))
            )
            && def.type === "object"
            && (def.required || []).every(k => typeof k == 'string')
            && Object.values(def.properties).every(is_type.expr))
            return Object.fromEntries(Object.entries(def.properties).map(([n, v]) => [n, is_type.expr(v)]));
        return false;
    },
    
    variant: def => {
        let doc = def.description;
        if (exporters.enum.guard(def))
            return def.enum.map(e => ({
                kind: 'variant',
                name: e,
                payloadKind: 'empty',
                payload: null,
                doc,
            }));
        if (exact_keys(def, 'type', 'required', 'properties')
            && def.type === 'object'
            && Object.values(def.properties).length == 1
           ){
            let [name, value] = Object.entries(def.properties)[0];
            if (is_type.expr(value))
                return [{
                    kind: 'variant',
                    payloadKind: 'expr',
                    name,
                    payload: is_type.expr(value),
                    doc,
                }];
            if (is_type.record(value))
                return [{
                    kind: 'variant',
                    name,
                    payloadKind: 'record',
                    payload: is_type.record(value),
                    doc,
                }];
        }
        return false;
    },
};

// for (let k in is_type) {
//     is_type[k] = trace1(k, is_type[k]);
// }

// let trace = (name, f) => (...inputs) => {
//     let output = f(...inputs);
//     log_full({f: name, inputs, output});
//     return output;
// };

let export_record = (fields, path) => {
    let record_expression = fields.map(([field, type], i) => {
        let p = [...path, 'field_'+field];
        let sub = mk_match('x', ocaml_arms_of_type_expr(type, p), p);
        let match = `match List.assoc_opt "${field}" l with Option.Some x -> begin ${sub} end | Option.None -> raise (MissingField {field = "${field}"; fields = l})`;
        return `${fieldNameOf(field)} = begin ${match} end`;
    }).join(';\n');
    return [`\`Assoc l`, `{ ${record_expression} }`];
};

let mkdoc = doc => doc ? ` (** ${doc} *)` : '';

let exporters = {
    oneOf: {
        guard: def => eq(keys(def), new Set(["oneOf"])) &&
            def.oneOf.every(is_type.variant),
        f: (name, {oneOf}) => {
            let variants = oneOf.map(is_type.variant).flat();
            let type = variants.map(({kind, name: variant_name, payloadKind, payload, doc}) => {
                doc = mkdoc(doc);
                let variant = ensureUnique('variant', variantNameOf(variant_name));
                return ({
                    record: () => {
                        let fields = Object.entries(payload).map(([field, value]) =>
                            fieldNameOf(field) + ' : ' + ocaml_of_type_expr(value, ['rec-variant:'+variant+':'+field]));
                        return `${variant} of {${fields.join(';\n')}}${doc}`;
                    },
                    expr: () => `${variant} of (${ocaml_of_type_expr(payload, ['expr-variant:'+variant+':'+name])})${doc}`,
                    empty: () => `${variant}${doc}`,
                }[payloadKind] || (() => {
                    throw "bad payloadKind: " + payloadKind;
                }))();
            }).join('\n     | ');
            let parse_arms = variants.map(({kind, name: variant_name, payloadKind, payload}) => {
                let variant = variantNameOf(variant_name);
                let wrap = (arms, prefix='') => [
                    [`\`Assoc ["${variant_name}", rec_value]`,
                     prefix + mk_match('rec_value', arms, ['rec-variant_'+variant+'_'+variant_name])
                    ]
                ];
                return ({
                    record: () => {
                        let [pat, expr] = export_record(Object.entries(payload), ['rec-variant_'+variant+'_'+variant_name]);
                        return wrap([[pat, variant+' '+expr]]);
                    },
                    expr: () => wrap(ocaml_arms_of_type_expr(payload, ['expr-variant(PA):'+name+':'+variant+':'+variant_name]), variant + ' '),
                    empty: () => [[`\`String "${variant_name}"`, variant]],
                }[payloadKind] || (() => {
                    throw "bad payloadKind: " + payloadKind;
                }))();
            }).flat();
            let parse = mk_match('o', parse_arms, ['parse_'+name]);
            let to_json = `match o with ${variants.map(({kind, name: variant_name, payloadKind, payload}) => {
                let variant = variantNameOf(variant_name);
                let wrap = (x, e) => `${variant} ${x} -> \`Assoc ["${variant_name}", ${e}]`;
                return ({
                    record: () => {
                        let fields = Object.entries(payload);
                        return wrap(
                          `{${fields.map(([field, type], i) => `${fieldNameOf(field)}`).join('; ')}}`,
                          `\`Assoc [${
                              fields.map(([field, type], i) => `("${field}", ${ocaml_yojson_of_type_expr(type, fieldNameOf(field), [name+':'+variant, 'variant', field])})`).join('; ')
                          }]`
                        );
                    },
                    expr: () => wrap('x', ocaml_yojson_of_type_expr(payload, 'x', [name+':'+variant, 'payload'])),
                    empty: () => `${variant} -> \`String "${variant_name}"`,
                }[payloadKind] || (() => {
                    throw "bad payloadKind: " + payloadKind;
                }))();
            }).join(' | ')}`;
            return {type, parse, to_json};
        },
    },
    // object is a *flat* record
    object: {
        guard: def => (eq(keys(def), new Set(["type", "required", "properties"]))
                       || eq(keys(def), new Set(["type", "properties"]))
                      ) 
            && def.type === "object"
            && (def.required || []).every(k => typeof k == 'string')
            && Object.values(def.properties).every(is_type.expr),
        f: (name, {required, properties}) => {
            let fields = Object.entries(properties).map(
                ([name, prop]) => [name, is_type.expr(prop), prop.description]
            );

            let [pat, expr] = export_record(fields, ['struct_'+name]);
            
            return {
                type: `{ ${fields.map(([fname, type, doc]) => `${fieldNameOf(fname)} : ${ocaml_of_type_expr(type, ['struct_'+fname+'_'+name])}${mkdoc(doc)}`).join(';\n')} }`,
                parse: mk_match('o', [[pat, expr]], ['struct_'+name]),
                to_json: //`let {${fields.map(([fname, type, doc]) => fieldNameOf(fname)).join(';')}} = o in`
                   `\`Assoc [${fields.map(([fname, type, doc]) => `("${fname}", ${ocaml_yojson_of_type_expr(type, 'o.'+fieldNameOf(fname), ['todo'])})`).join('; ')}]`
            };
        },
    },
    enum: {
        guard: def => eq(keys(def), new Set(["type", "enum"]))
            && def.type == "string",
        f: (name, o) => {
            assert(o.enum.every(x => typeof x == "string"), 'not every enum is a string');

            let variants = o.enum.map(n => ({
                Δ: n,
                variant: ensureUnique('variant', variantNameOf(n)),
                variantOriginName: n
            }));

            let parse_string
                = `match s with ` + variants.map(
                    ({Δ, variant}) => `"${Δ}" -> ${variant}`
                ).join(' | ') + ` | s -> failwith ("unexpected variant [" ^ s ^ "] while parsing enum [${name}]")`;
            
            return {
                type: variants.map(({variant}) => variant).join(' | '),
                parse: `  match o with
                        | \`String s -> (${parse_string})
                        | _ -> failwith "expected a string while parsing a ${name}"
                       `,
                to_json: `match o with ${variants.map(({variant, variantOriginName}) => `${variant} -> \`String "${variantOriginName}"`).join(' | ')}`,
            };
        },
    },
};

let export_definition = (name, def) => {
    let suitable_exporters = Object.entries(exporters).filter(
        ([_, {guard}]) => guard(def)
    );

    if (suitable_exporters.length != 1){
        console.error(`ERROR: each definition should have exactly one suited exporter, but type "${name}" has the following exporter(s): ${JSON.stringify(suitable_exporters.map(([n, _]) => n))}.`);
        console.error('name', name);
        log_full(def);
        console.error('xname', name);
        
        throw "kind error";
    }
    let [_, {f}] = suitable_exporters[0];
    name = ensureUnique('type', typeNameOf(name));
    let r = f(name, def);
    if(r === null)
        return `(* type ${name} *)`;
    let {type, parse, to_json} = r;
    return {name, type, parse, to_json};
    // return [{type, parse}]
    // return `type ${name} = ${type}\nlet parse_${name} (o: Yojson.Safe.t): ${name} = ${parse}\n`;
};

function run(str){
    let contents = JSON.parse(str);
    const definitions = clean(contents.definitions);
    
    let output_string = `include struct
[@@@warning "-A"]`;

    let items = Object.entries(definitions).map(
        ([name, def]) => export_definition(name, def)
    ).filter(x => x instanceof Object);

    let derive_items = ['show', 'eq'];

    output_string += `
module ParseError = struct
  exception MissingField of {
    fields: (string * Yojson.Safe.t) list;
    field: string
  }

  let pp = function
    | MissingField {fields; field} ->
       "Missing field [" ^ field ^ "], while looking at the following JSON: " ^ Yojson.Safe.pretty_to_string (\`Assoc fields)
    | e -> raise e
end

open ParseError
`;

    output_string += ('type ' + items.map(({name, type}) =>
        `${name} = ${type}\n${derive_items.length ? `[@@deriving ${derive_items.join(', ')}]` : ''}`).join('\nand ')
    );
    output_string += ('');
    output_string += ('let rec ' + items.map(({name, type, parse}) =>
        `parse_${name} (o: Yojson.Safe.t): ${name} = ${parse}`
    ).join('\nand '));
    output_string += ('');
    output_string += ('let rec ' + items.map(({name, type, parse, to_json}) =>
        `to_json_${name} (o: ${name}): Yojson.Safe.t = ${to_json}`
    ).join('\nand '));

    return output_string + ' \n end';
}

function parse_args(){
    let [script_name, input_path, output_path, ...rest] = process.argv.slice(1);
    if(!input_path || !output_path || rest.length) {
        console.log(`
Usage: node ${script_name} INPUT_PATH OUTPUT_PATH

   INPUT_PATH and OUTPUT_PATH can be - to denotes stdin or stdout
`);
        process.exit();
    }
    return { input_path, output_path };
}

async function read(stream) {
    const chunks = [];
    for await (const chunk of stream) chunks.push(chunk); 
    return Buffer.concat(chunks).toString('utf8');
}

async function main(){
    const fs = require('fs');
    let {input_path, output_path} = parse_args();
    let out = run(input_path == '-'
                  ? await read(process.stdin)
                  : fs.readFileSync(input_path, 'utf-8')
                 );
    output_path == '-'
        ? process.stdout.write(out)
        : fs.writeFileSync(output_path, out);
}

main();

