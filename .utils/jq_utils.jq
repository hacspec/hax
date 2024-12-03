# Removes a field from an object at any depth
def remove_field(field):
    walk(if type == "object" and has(field) then del(.[field]) else . end);

# Remove `table_id` indirections whenever a value is found
def thir_drop_table_id_nodes:
    walk(if type == "object" and has("cache_id") and has("value") and .value then .value else . end);

# Prints a THIR def_id as a string, useful for searching
def thir_str_of_def_id_contents:
  (
      [.krate]
    + [
          .path.[]
        | try (.disambiguator as $d | .data | . as $data | keys | .[0] | $data[.] + (if $d > 0 then "#" + $d else "" end))
        | select(type == "string")]
  ) | join("::");

# Prints all THIR def_ids
def thir_str_of_def_ids:
     thir_drop_table_id_nodes | walk(
          # if type == "object" and has("contents") and (.contents | type) == "object" and .contents | has("krate") and .contents | has("path") then
          if try(. as $o | ($o.contents.krate | type == "string") and ($o.contents.path | type == "array")) catch false then
            .contents | thir_str_of_def_id_contents
          else
            .
          end);
