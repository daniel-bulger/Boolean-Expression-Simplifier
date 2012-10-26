#include <iostream>
#include <cstdlib>
#include <vector>
#include <sys/time.h>
#include <algorithm>
#include <stdio.h>
#include <ctype.h>
#include "Expression.cpp"
using namespace std;
Expression* parseBooleanExpression(string booleanExpression){ // recursive function to parse a boolean expression
    // Expressions will be nested to some unknown level, so we will first determine each statement's depth
    booleanExpression.erase(std::remove_if(booleanExpression.begin(), booleanExpression.end(), ::isspace), booleanExpression.end());
    Expression* mainConnective = new Expression();
    static const char disjunction_arr[] = {'|','+'};
    vector<char> disjunctions(disjunction_arr, disjunction_arr + sizeof(disjunction_arr) / sizeof(disjunction_arr[0]) );
    static const char conjunction_arr[] = {'^','&','*'};
    vector<char> conjunctions(conjunction_arr, conjunction_arr + sizeof(conjunction_arr) / sizeof(conjunction_arr[0]) );
    static const char negation_arr[] = {'~','!','-'};
    vector<char> negations(negation_arr, negation_arr + sizeof(negation_arr) / sizeof(negation_arr[0]) );
    //static const char negation_arr_postfix[] = {'\''};
    //vector<char> negations_postfix(negation_arr_postfix, negation_arr_postfix + sizeof(negation_arr_postfix) / sizeof(negation_arr_postfix[0]) );

    int depth = 0; // keeps track of how deep we are in the expression so we know where the main connective is
    bool depth_reached_zero = false;
    while(booleanExpression[0] == '(' && booleanExpression[booleanExpression.length()-1]==')' && depth_reached_zero == false){
        depth = 1;
        depth_reached_zero = false;
        for(int i = 1; i < booleanExpression.length()-2;i++){
            if(booleanExpression[i] == '('){ // if we see a begin paren, we are going deeper
                depth++;
            }
            if(booleanExpression[i] == ')'){ //  if we see an end paren, we are going out
                depth--;
            }
            if(depth == 0){
                depth_reached_zero = true;
            }
        }
        if(!depth_reached_zero){
            booleanExpression = booleanExpression.substr(1,booleanExpression.length()-2);
        }
    }
    depth = 0;
    // now we should have a statement without parens surrounding it
    if(booleanExpression.length()==1){ // if the expression is merely an atomic statement
        mainConnective->symbol = booleanExpression[0]; // make the main connective an atomic symbol
        return mainConnective;
    }
    for(int i = 0; i < booleanExpression.length();i++){
        if(depth == 0){
            if(find(conjunctions.begin(),conjunctions.end(),booleanExpression[i]) != conjunctions.end()){
                mainConnective->Expression_type = Expression::AND;
                mainConnective->operands.push_back(parseBooleanExpression(booleanExpression.substr(0,i))); // create first operand
                mainConnective->operands.push_back(parseBooleanExpression(booleanExpression.substr(i+1,booleanExpression.length())));
                // create second operand
                return mainConnective;
            }
            if(find(disjunctions.begin(),disjunctions.end(),booleanExpression[i]) != disjunctions.end()){
                mainConnective->Expression_type = Expression::OR;
                mainConnective->operands.push_back(parseBooleanExpression(booleanExpression.substr(0,i))); // create first operand
                mainConnective->operands.push_back(parseBooleanExpression(booleanExpression.substr(i+1,booleanExpression.length())));
                // create second operand
                return mainConnective;
            }
        }
        if(booleanExpression[i] == '('){ // if we see a begin paren, we are going deeper
            depth++;
        }
        if(booleanExpression[i] == ')'){ //  if we see an end paren, we are going out
            depth--;
        }
    }
    depth = 0;
    for(int i = 0; i< booleanExpression.length();i++){
        if(depth == 0){
            if(find(negations.begin(),negations.end(),booleanExpression[i]) != negations.end()){
                mainConnective->Expression_type = Expression::NOT;
                mainConnective->operands.push_back(parseBooleanExpression(booleanExpression.substr(i+1,booleanExpression.length())));
                // create only operand
                return mainConnective;
            }
            /*if(find(negations_postfix.begin(),negations_postfix.end(),booleanExpression[i]) != negations_postfix.end()){
                mainConnective->Expression_type = Expression::NOT;
                mainConnective->operands.push_back(parseBooleanExpression(booleanExpression.substr(0,i)));
                // create only operand
                return mainConnective;
            }*/
        }
        if(booleanExpression[i] == '('){ // if we see a begin paren, we are going deeper
            depth++;
        }
        if(booleanExpression[i] == ')'){ //  if we see an end paren, we are going out
            depth--;
        }
    }
    cerr << "Error: invalid function syntax" << endl;
    exit(1); 
}
int main(int argc, char* argv[]){
    string booleanExpression;
    if(argc == 2){
        booleanExpression = argv[1];
    }
    else{
        cin >> booleanExpression;
    }
    cout << "\\documentclass{article}" << endl;
    cout << "\\usepackage{amsmath} " << endl;
    cout << "\\newcommand\\textbox[1]{%" << endl;
    cout << "\\parbox{.333\\textwidth}{#1}%" << endl;
    cout << "}" << endl;
    cout << "\\begin{document}" << endl;
    Expression* outerExpression = parseBooleanExpression(booleanExpression);
    outerExpression->clean();
    cout << "\\title{The simplification of $" << outerExpression->getExpressionHumanReadable()<< "$}" << endl;
    cout << "\\author{Daniel Bulger}\\maketitle" << endl;
    cout << "\\begin{equation}" << endl;
    outerExpression->printExpressionHumanReadable();
    cout << "\\end{equation}" << endl;
    while(outerExpression->simplify()){
        outerExpression->clean();
        cout << "\\begin{equation}" << endl;
        outerExpression->printExpressionHumanReadable();
        cout << "\\end{equation}" << endl;
            // simplifies the expression until it can be simplified no more
    }
    cout << "\\\\\\noindent \\textbox{ Final expression: \\hfill} \\textbox{\\hfil $ " << outerExpression->getExpressionHumanReadable() << " $ \\hfil} \\textbox{\\hfill}"  << endl;

    cout << "\\end{document}" << endl;
    return 0;
}
