INPUT_EXPRESSION=""
OUTPUTFILE="./output"
if [ $# -ge 1 ]
    then
    INPUT_EXPRESSION=$1
    if [ $# -eq 2 ]
        then
        OUTPUTFILE="$2"
    fi
fi
OUTPUTFILE=`basename $OUTPUTFILE ".pdf"`
C++/boolEval "$INPUT_EXPRESSION" > "./Tex Output/output.tex"
if [ $? -eq 0 ]; #normal exit
    then
    mkdir "Tex Output"
    cd "Tex Output"
    latex "-output-format=pdf" "./output.tex" 
    cd ../
    mv "Tex Output/output.pdf" "$OUTPUTFILE.pdf"
    xdg-open "$OUTPUTFILE.pdf"
fi
