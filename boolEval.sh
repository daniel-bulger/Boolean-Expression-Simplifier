INPUT_EXPRESSION=""
OUTPUTFILE="./Tex Output/output.tex"
echo $#
if [ $# -ge 1 ]
    then
    echo $1
    INPUT_EXPRESSION=$1
    if [ $# -eq 2 ]
        then
        OUTPUTFILE=$2
    fi
fi

C++/boolEval $INPUT_EXPRESSION > "$OUTPUTFILE"
if [ $? -eq 0 ]; #normal exit
    then
    cd "Tex Output"
    latex "./output.tex"
    xdg-open "./output.dvi"
    cd ../
fi
