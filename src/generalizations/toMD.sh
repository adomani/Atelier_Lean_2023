#! /bin/bash

##  `toMD <file>` performs substitutions to convert lean-comments to md-text and
##  lean code to md codeblocks.
toMD () {
  sed -z '
    s=\n--  *\([^\n]*\)=\n```\n\1\n```lean=g  # replace =-- [rest]= with =```\n[rest]```lean=
    s=^--  *\([^\n]*\)=\1```lean=             # as above, but at the beginning of file
    s=\n/-[\n]*=```\n=g                       # replace =/-= with =```=
    s=^[\n]*/-[\n]*==g                        # as above, but at the beginning of file
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

##  `nonIOnls <cslist>` generates the sed-ready replacements for adding a line break before
##  each line beginning with one of the comma-separated-values in `<cslist>`
nonIOnls () {
  local IFS kw
  IFS=$'\n'
  for kw in ${1//,/$'\n'}; do
    printf '  s=\\n%s=\\n&=g\n' "$kw"
  done
}

##  `nls` generates the sed-replacements to add line breaks before several Lean-specific words
nls () { nonIOnls "namespace,variable,theorem,lemma,example,open,section,end ,#" ; }

##  `rmComments <file>` removes all Lean-comments from `<file>` and does some small reformatting
##  of the result, mostly dealing with reorganizing line-breaks.
rmComments () {
  sed -z '
    s=[^/]--[^\n]*==g          ##  remove lines beginning with `--`
    s=^--[^\n]*==g             ##  remove lines beginning with `--`
    s=/-\([^-]\|-[^/]\)*-/==g  ##  replace text inside `/-...-/`: matches (either not-`-` or `-`-and-not-`/`)*
    s=  *\n=\n=g               ##  remove spaces before line breaks
    s=^\n[\n]*==g              ##  remove all line breaks at the beginning of a file
    s=\n\n[\n]*=\n=g           ##  condense consecutive line breaks into a single one
    s=^\(  *\){\n\1 =\1{=g     ##  replace `  {\n    [stuff]` with `  { [stuff]` at the beginning
    s=\n\(  *\){\n\1 =\n\1{=g  ##  replace `  {\n    [stuff]` with `  { [stuff]` and in the middle
    s=\n  *}= }=g              ##  replace `\n  }` with ` }`
  '"$(nls)" "${1}"             ##  add back in some Lean-specific line breaks
}
