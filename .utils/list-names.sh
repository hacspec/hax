#!/usr/bin/env bash

function pager() {
    if command -v bat &> /dev/null; then
        bat -l ml
    else
        less
    fi
}

hax-engine-names-extract | sed '/include .val/,$d' | pager
