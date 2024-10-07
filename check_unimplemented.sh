
, gh issue -R hacspec/hax list --label 'marked-unimplemented' --json number,closed -L 100 | jq '.[] | select(.closed | not) | .number' | sort -u > /tmp/marked-unimplemented.json

rg 'issue_id:(\d+)' -Ior '$1' | sort -u > /tmp/found.json

diff -U0 /tmp/marked-unimplemented.json /tmp/found.json \
    | rg '^[+-]\d' \
    | sd '[-](\d+)' '#$1\t is labeled `marked-unimplemented`, but was not found in the code' \
    | sd '[+](\d+)' '#$1\t is *not* labeled `marked-unimplemented` or is closed'
