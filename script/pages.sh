mkdir -p content/modules
for file in $(find . -name "*.lhs"); do
    BASENAME=$(basename $file ".lhs")
    DEST=content/modules/$BASENAME.md
    echo "---" > $DEST
    echo "title: Module \"$BASENAME\"" >> $DEST
    echo "date: $(git log -1 --pretty="format:%ci" $file)" >> $DEST
    echo "summary: $(cat desc/$BASENAME.txt)" >> $DEST
    echo "---" >> $DEST
    ${0%/*}/markdown.sh $file >> $DEST
done
