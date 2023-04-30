printf $'a\n## `b_c_d`\n`e_f` g_h\n' | texConversions -


outerret $'printf \'a\n## `b_c_d`\n`e_f` g_h\n\' | texConversions -' $'a\n\begin{frame}[fragile]{{\verb{\texttt{b\\_c\\_d}}}\n{\verb`e_f`} g_h\n' '' 0


printf $'`a`\n`b` c\n' | replaceXWithLR '`' 'lx`' '`rx' -


grep " *|[ |-:]*" ../topics.md
