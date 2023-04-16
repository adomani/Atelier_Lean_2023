#!/bin/bash

##  `getLinkRef <file>` extracts the content of each
##  "second consecutive square bracket", one per line.
##  For instance
##  ```
##  printf 'text [1][2], more text, [3][4]\n[5][6]' | getLinkRef -
##  > 2\n4\n6\n
##  ```
getLinkRef () {
  sed -n 's=[^[]*\[[^]]*\]\[\([^]]*\)\][^[]*=\1\n=gp' "${1}" |
    tr --squeeze-repeats "\n" "\n"
}

if [ "$(whoami)" == "damiano" ]; then
  .  ~/Setup/Tests/testtest.sh
  outerret 'printf "text [1][2], more text, [3][4]\n[5][6]" | getLinkRef -' $'2\n4\n6\n' '' 0
fi

##  `mkLink <file>` searches for `<file>.lean` starting from the git root directory
##  returns the url for opening `<file>.lean` with the lean-web-editor.
##  `mkLink` also assigns as "hover name" to the link the name of the file:
##  * replaces underscores (`_`) by spaces (` `);
##  * inserts a space in each consecutive lowercase-uppercase pair.
##  For instance `OneTwo_ThreeFour` becomes `One Two Three Four`).
mkLink () {
  local pth repo url url1 url2 hover penc
  pth="$(git rev-parse --show-toplevel)"
  repo="$(git config --get remote.origin.url | sed 's=.*github\.com/==; s=\.git$==')"
  url1='https://leanprover-community.github.io/lean-web-editor/'
  url2='#url=https://raw.githubusercontent.com/'"$repo"'/master'
  url="$url1$url2"
  penc="$(find "${pth}" -name "${1}.lean" | sed "s|${pth}|${url}|"'; s/ /%20/g')"
  [ -z "${penc}" ] && >&2 printf 'File `%s.lean` not found\n' "${1}"
  hover="$(printf %s "${1}" | sed 's/_/ /g ; s/\([a-z]\)\([A-Z]\)/\1 \2/g')"
  printf '[%s]: %s "%s"\n' "${1}" "${penc}" "${hover}"
}

##  `allLinks <file>` extracts the md-encoded url-refs from `<file>` and
##  produces the actual url links.
allLinks () {
  (
    cd "$(git rev-parse --show-toplevel)" || { >&2 printf 'allLinks: `cd` failed' ; return 1 ; }
    printf '<!--  Autogenerated links  -->\n'
    printf '<!--  `autolinks` removes modifications from here on  -->\n\n'
    IFS=$'\n'
    for fil in $(getLinkRef "$(basename "${1}")"); do
      mkLink "${fil}"
    done
  )
}

##  `autolinksSafe <file>` acts like `autolinks <file>`, but prints to stdout
##  instead of modifying `<file>`.
autolinksSafe () {
  sed '/^<!--  Autogenerated links  -->$/Q' "${1}" &&
    allLinks "${1}"
}

##  `autolinks <file>` extracts the link references from `<file>`,
##  for each `<ref>` searches for `<ref>.lean`,
##  removes from `<file>` everything after `<!--  Autogenerated links  -->` and
##  recreates the end of `<file>` with all the generated links.
autolinks () {
  if [ -z "${1}" ]; then
    >&2 printf 'Usage: autolinks FILE\n'
    return 1
  fi
  if ! diff -q <(autolinksSafe "${1}") "${1}" > /dev/null; then
    local con=0
    while [ -f "$con" ]; do ((con++)); done
    autolinksSafe "${1}" > "${con}" &&
      mv "${con}" "${1}"
  fi
}

##  `checkUnlinkedFiles <file>` prints the `.lean` files that are not
##  referenced in `<file>`.
checkUnlinkedFiles () {
  local fil outp
  outp="$({
    for fil in $(getLinkRef "${1}"); do
      printf './src/%s.lean\n' "$fil"
    done
    find . -type f -name "*.lean" -a -not -path "./_target*"
  } | sort | uniq -u)"
  [ -n "${outp}" ] && >&2 printf '`.lean` files that are not referenced in %s:\n\n%s\n\n' "${1}" "${outp}"
}

##  `getURLs <file>` extracts the URLs in `<file>`, except for the ones
##  linking to `lean-web-editor`.
getURLs () {
  grep -o "http[^ )]*" "${1}" |
    grep -v "https://leanprover-community.github.io/lean-web-editor/"
}

## `checkURL <url>` has exit code 0 exactly when `<url>` is an existing url.
checkURL () { wget --spider "${1}" 2>/dev/null ; }

## `checkURLs <file>` verifies if the urls in `<file>` work.
checkURLs () {
  if [ -z "${1}" ]; then
    >&2 printf 'Usage: checkURLs FILE\n'
    return 1
  fi
  local err ur IFS=$'\n'
  err=""
  for ur in $(getURLs "${1}"); do
    if ! checkURL "${ur}"; then
      err="${err}${url}\n"
    fi
  done
  if [ -z "${err}" ]; then
    printf 'All non-lean-web-editor links are working!\n'
  else
    printf 'Non-working links\n\n%s' "${err}"
  fi
}

checkAll () {
  if [ -z "${1}" ]; then
    >&2 printf 'Usage: checkAll FILE\n'
    return 1
  fi
  printf 'Checking URLs\n'
  checkURLs "${1}"
  printf '\nChecking unlinked files\n'
  checkUnlinkedFiles "${1}"
}
