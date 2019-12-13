BEGIN { del=0 }
/^\\coqlibrary/ { del=1 }
del<=0 { print }
del>0 && match($0, /^\\section(.*)/, a) { del -= 1; print "\\chapter"a[1] }
END { print "\\end{document}" }
