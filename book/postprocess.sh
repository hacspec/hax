#!/usr/bin/env sh

# This file replaces `<strong>user-checkable</strong>` with actual
# checkboxes and adds CSS to the generated HTML.

for file in $(find . -name '*.html'); do
    sed -i 's|<strong>user-checkable</strong>|<input type="checkbox" class="user-checkable"/>|g' "$file"
done

for css in $(find . -name 'general.css'); do
    cat >> "$css" <<-EOF
input.user-checkable {
    transform: scale(1.5);
    margin-right: 8px;
    margin-left: 8px;
}

ul:has(> li > .user-checkable) {
    list-style-type: none;
    padding: 0;
    margin: 0;
}
li:has(> .user-checkable) {
    list-style-type: none;
    padding: 0;
    margin: 0;
}
EOF
done
