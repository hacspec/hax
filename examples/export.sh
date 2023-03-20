case "$1" in
    thir-export);;
    circus);;
    thir-elab);;
    *)
        printf "Usage: \033[1m%s action\033[0m\n" "$s";
        printf "  where \033[1maction\033[0m is \033[1mthir-export\033[0m, \033[1mcircus\033[0m or \033[1mthir-elab\033[0m\n"
        exit 1
esac

for i in */Cargo.toml; do
    name=$(cat "$i" | tomlq '.package.name' -r)
    json="json-output/$name.json"
    fstar_out="fstar-extraction"
    printf "Crate: \033[1m%s\033[0m\n" "$name";
    case "$1" in
        thir-export)
            cargo thir-export \
                  -i '**::array' -i '**::bytes' -i '**::public_bytes' \
                  -i '**::public_nat_mod' -i '**::unsigned_public_integer' \
                  -C -p "$name" \; \
                  -o "$json"
            ;;
        circus)
            cargo circus \
                  -i '**::array' -i '**::bytes' -i '**::public_bytes' \
                  -i '**::public_nat_mod' -i '**::unsigned_public_integer' \
                  -C -p "$name" \; \
                  -o "$fstar_out" \
                  fstar
            ;;
        thir-elab)
            thir-elab \
                fstar \
                --input "$json" \
                --output "$fstar_out"
        ;;
    esac
done
