pandoc -f markdown+lhs $1 -t markdown --wrap=preserve | sed 's/{{\\</{{</g;s/\\>}}/>}}/g'
