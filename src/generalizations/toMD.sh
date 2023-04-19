#! /bin/bash

##  `toMD <file>` performs substitutions to convert lean-comments to md-text and
##  lean code to md codeblocks.
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

##  `mkmd` calls `toMD` on each `.lean` file in the current directory, checks whether
##  the corresponding `.md` file differs and, if it does, then it replaces with the
##  output of `toMD`.
mkmd () {
  local fil
  for fil in *.lean; do
    if diff -q <(toMD "${fil}") "${fil/%.lean/.md}" > /dev/null ; then
      brown 'Not changing '; printf '%s\n' "${fil/%.lean/.md}"
    else
      brown 'Updating '; printf '%s\n' "${fil/%.lean/.md}"
      toMD "${fil}" > "${fil/%.lean/.md}"
    fi
  done
}
