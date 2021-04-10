pandoc -f markdown+lhs-smart $1 -t commonmark --wrap=preserve | sed 's/{{\\</{{</g;s/\\>}}/>}}/g'
