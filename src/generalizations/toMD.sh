#! /bin/bash

toMD () {
  sed -z '
    s=\n--  *\([^\n]*\)=\n```\n\1\n```lean=g  # replace =-- [rest]= with =```\n[rest]```lean=
    s=^--  *\([^\n]*\)=\1```lean=             # as above, but at the beginning of file
    s=/-[\n]*=```\n=g                         # replace =/-= with =```=
    s=[\n]*-/[\n]*=\n\n```lean\n=g            # replace =-/= with =```lean=
    s=```lean[\n]*```==g                      # remove consecutive =```lean= =```= pairs
    s=[\n]*```\n=\n```\n=g                    # remove trailing line breaks inside code blocks
    s=[\n]*```lean=\n\n```lean=g              # separate code-blocks by two line breaks before
    s=```\n[\n]*=```\n\n=g                    # separate code-blocks by two line breaks after
  ' "${1}"
}
