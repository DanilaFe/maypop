for file in $(find . -name "*.lhs"); do
    BASENAME=$(basename $file ".lhs")
    DEST=$1/content/modules/$BASENAME.md
    echo "---" > $DEST
    echo "title: Module \"$BASENAME\"" >> $DEST
    echo "date: $(git log -1 --pretty="format:%ci" $file)" >> $DEST
    echo "---" >> $DEST
    ${0%/*}/markdown.sh $file >> $DEST
done
