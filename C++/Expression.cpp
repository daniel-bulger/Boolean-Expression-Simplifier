#include "Expression.h"
#include <vector>
#include <set>
#include <cmath>
#include <numeric>
#include <utility>
using namespace std;
void printTransformation(const Expression& from , const Expression& to , const string method);
vector<string> Expression::inference_rules;
bool Expression::suppress_output;
/*bool Expression::operator<(const Expression& other) const{ 
    if(*this == other){
        return false;
    }
    // This operator is arbitrary, but is used internally for stl operations to determine equivalence
        if(operands.size() != other.operands.size()){
            return operands.size() < other.operands.size();
        }
        if((Expression_type == Expression::AND) && (other.Expression_type == Expression::OR)){
            return false;
        }
        if((Expression_type == Expression::OR) && (other.Expression_type == Expression::AND)){
            return true;
        }
        if(operands.size()==0 && other.operands.size()==0){
            return symbol < other.symbol;
        }
        vector<Expression*> lhs_ops_sorted = this->operands;
        sort(lhs_ops_sorted.begin(),lhs_ops_sorted.end(),ExpressionComparator());
        vector<Expression*> rhs_ops_sorted = other.operands;
        sort(rhs_ops_sorted.begin(),rhs_ops_sorted.end(),ExpressionComparator());
        double number_less = 0.0;
        for(int i = 0; i < operands.size(); i++){
            if(*(lhs_ops_sorted[i]) < *(rhs_ops_sorted[i])){
                number_less+= pow(2,i);
            }
        }
        if(number_less > pow(2,operands.size()-1)){
            return true;
        }
        return false;
    }*/
void Expression::simplifyCompletely(){
    while(simplify()){} // simplify until we can simplify no more
}
bool Expression::simplify(){
    clean();
    /* It is necessary that we apply the 'best' inference rule possible, regardless of where it is in the tree */
    for(int i = 0; i<inference_rules.size();i++){ // attempt to apply each inference rule until we find one we can apply
        if(applyInferenceRule(i)){ // if we successfully applied the rule
            return true; // do nothing else, we only want to apply one rule per simplification
        }
        /* If we are unable to apply a rule at this level, we will go down one level*/
    }
    return false;
}
bool Expression::applyInferenceRule(int i){
    /* We first attempt to apply the inference rule directly to the current statement*/
    if(directlyApplyInferenceRule(i)){
        return i;
    }
    else{
        if(Expression_type == Expression::ATOMIC){ // if the statement is atomic
            return 0;
            // Nothing to do here... we are done
        }
        for(int j = 0; j<operands.size();j++){ // otherwise, try to apply the rule to all children
            if(operands[j]->applyInferenceRule(i)){ // if the rule can be applied to any child
                return i; // we are done
            }
        }
    }
    return false;
}
bool Expression::directlyApplyInferenceRule(int i){
    /* The outer conditionals determine which inference rule should be attempted on the expression */
    if(inference_rules[i] == "eliminate_implication"){
        if(Expression_type == Expression::IMPLICATION){
            Expression* old_expression = new Expression();
            *old_expression = *this;
            Expression_type = Expression::OR;
            Expression* negation_wrapper = new Expression();
            negation_wrapper->Expression_type = Expression::NOT;
            negation_wrapper->operands.push_back(operands[0]);
            *(operands[0]) = *negation_wrapper;
            printTransformation(*this, *(operands[i]->operands[i]), Expression::inference_rules[i]);            
        }
    }
    if(inference_rules[i] == "double negation"){ // attempt to apply the double negation rule
        if(Expression_type == Expression::NOT && operands[0]->Expression_type == Expression::NOT){
            printTransformation(*this, *(operands[i]->operands[i]), Expression::inference_rules[i]);
            *this = *(operands[i]->operands[i]);
            return true;
        }
    }
    if(inference_rules[i] == "contradiction"){
        if(Expression_type == Expression::AND){
            vector<Expression> operand_representations;
            Expression* opposite_expression;
            for(int j = 0; j < operands.size(); j++){
                operand_representations.push_back(*(operands[j]));
            }
            for(int j = 0; j < operands.size(); j++){
                Expression* temp_expr_ptr = operands[j];
                opposite_expression = new Expression();
                opposite_expression->Expression_type = Expression::NOT;
                opposite_expression->operands.push_back(temp_expr_ptr);
                if(find(operand_representations.begin(),operand_representations.end(),*(opposite_expression)) != operand_representations.end()) {
                    Expression* new_contradiction = new Expression();
                    new_contradiction->Expression_type = Expression::ATOMIC;
                    new_contradiction->symbol = '0';
                    printTransformation(*this, *new_contradiction, Expression::inference_rules[i]);
                    *this = *new_contradiction;
                    return true;
                }
            }
        }
    }
    if(inference_rules[i] == "tautology"){
        if(Expression_type == Expression::OR){
            vector<Expression> operand_representations;
            Expression* opposite_expression;
            for(int j = 0; j < operands.size(); j++){
                operand_representations.push_back(*(operands[j]));
            }
            for(int j = 0; j < operands.size(); j++){
                Expression* temp_expr_ptr = operands[j];
                opposite_expression = new Expression();
                opposite_expression->Expression_type = Expression::NOT;
                opposite_expression->operands.push_back(temp_expr_ptr);
                if(find(operand_representations.begin(),operand_representations.end(),*(opposite_expression)) != operand_representations.end()) {
                    Expression* new_tautology = new Expression();
                    new_tautology->Expression_type = Expression::ATOMIC;
                    new_tautology->symbol = '1';
                    printTransformation(*this, *new_tautology, Expression::inference_rules[i]);
                    *this = *new_tautology;
                    return true;
                }
            }
        }
    }
    if(inference_rules[i] == "inverse" ){
        if(Expression_type == Expression::NOT){
            if(operands[0]->is_tautology()){
                Expression* new_contradiction = new Expression();
                new_contradiction->Expression_type = Expression::ATOMIC;
                new_contradiction->symbol = '0';
                printTransformation(*this, *new_contradiction, Expression::inference_rules[i]);
                *this = *new_contradiction;
                return true;
            }
            if(operands[0]->is_contradiction()){
                Expression* new_tautology = new Expression();
                new_tautology->Expression_type = Expression::ATOMIC;
                new_tautology->symbol = '1';
                printTransformation(*this, *new_tautology, Expression::inference_rules[i]);
                *this = *new_tautology;
                return true;
            }
        }
    }
    if(inference_rules[i] == "identity"){
        if(Expression_type == Expression::OR){
            for(int j = 0; j < operands.size(); j++){
                if(operands[j]->is_contradiction()){
                    Expression* new_expression = new Expression();
                    *new_expression = *this;
                    new_expression->operands.erase(new_expression->operands.begin()+j);
                    printTransformation(*this, *new_expression, Expression::inference_rules[i]);
                    *this = *new_expression;
                    return true;
                }
            }
        }
        if(Expression_type == Expression::AND){
            for(int j = 0; j < operands.size(); j++){
                if(operands[j]->is_tautology()){
                    Expression* new_expression = new Expression();
                    *new_expression = *this;
                    new_expression->operands.erase(new_expression->operands.begin()+j);
                    printTransformation(*this, *new_expression, Expression::inference_rules[i]);
                    *this = *new_expression;
                    return true;
                }
            }
        }
    }
    if(inference_rules[i] == "annihilation"){
        if(Expression_type == Expression::AND){
            for(int j = 0; j < operands.size(); j++){
                if(operands[j]->is_contradiction()){
                    Expression* new_expression = new Expression();
                    new_expression->Expression_type = Expression::ATOMIC;
                    new_expression->symbol = '0';
                    printTransformation(*this, *new_expression, Expression::inference_rules[i]);
                    *this = *new_expression;
                    return true;
                }
            }
        }
        if(Expression_type == Expression::OR){
            for(int j = 0; j < operands.size(); j++){
                if(operands[j]->is_tautology()){
                    Expression* new_expression = new Expression();
                    new_expression->Expression_type = Expression::ATOMIC;
                    new_expression->symbol = '1';
                    printTransformation(*this, *new_expression, Expression::inference_rules[i]);
                    *this = *new_expression;
                    return true;
                }
            }
        }
    }
    if(inference_rules[i] == "idepotence"){ // attempt to apply the idepotence rule
        if(Expression_type == Expression::AND || Expression_type == Expression::OR){ // this rule applies to ANDs and ORs only
            vector<Expression> operand_representations;
            Expression* duplicate_expression = NULL;
            for(int j = 0; j<operands.size();j++){
                if(find(operand_representations.begin(),operand_representations.end(),*(operands[j])) != operand_representations.end()) {
                    duplicate_expression = operands[j];
                    break;
                }
                operand_representations.push_back(*(operands[j]));
            }
            if(duplicate_expression != NULL){ // if a duplicate expression was found
                vector<Expression*> temporary_operand_list;
                Expression* new_expression = new Expression();
                *new_expression = *this;
                for(int j = 0; j<new_expression->operands.size();j++){
                    if(*(new_expression->operands[j]) == *duplicate_expression){
                        new_expression->operands.erase(new_expression->operands.begin()+j); // erase all operands who match the duplicate expression
                        j--;
                    }
                }
                if(new_expression->operands.size() == 0){
                    *new_expression = *(duplicate_expression); // if all operands matched the duplicate, the only thing left is the duplicate.
                }
                else{ // otherwise, add the symbol that had duplicates back in as one operand.
                    Expression* new_atom = new Expression();
                    new_atom = duplicate_expression;
                    new_expression->operands.push_back(new_atom);
                }
                printTransformation(*this, *new_expression, Expression::inference_rules[i]);
                *this = *new_expression;
                return true;
            }
        }
    }
    if(inference_rules[i]=="demorgan"){
        if(Expression_type == Expression::NOT){
            if(operands[0]->Expression_type == Expression::AND){
                Expression* old_expression = new Expression();
                *old_expression = *this;
                *this = *(operands[0]);
                Expression_type = Expression::OR;
                for(int j = 0; j < operands.size(); j++){
                    Expression* temp_expr_ptr = operands[j];
                    operands[j] = new Expression();
                    operands[j]->Expression_type = Expression::NOT;
                    operands[j]->operands.push_back(temp_expr_ptr);
                }
                printTransformation(*old_expression, *this, Expression::inference_rules[i]);
                return true;
            }
            if(operands[0]->Expression_type == Expression::OR){
                Expression* old_expression = new Expression();
                *old_expression = *this;
                *this = *(operands[0]);
                Expression_type = Expression::AND;
                for(int j = 0; j < operands.size(); j++){
                    Expression* temp_expr_ptr = operands[j];
                    operands[j] = new Expression();
                    operands[j]->Expression_type = Expression::NOT;
                    operands[j]->operands.push_back(temp_expr_ptr);
                }
                printTransformation(*old_expression, *this, Expression::inference_rules[i]);
                return true;
            }
        }
    }
    if(inference_rules[i]== "absorption"){ // attempt to apply the absorption rule
        bool accomplished_something = false;
        Expression* old_expression = new Expression();
        if(Expression_type == Expression::AND || Expression_type == Expression::OR){ // this rule applies to ANDs and ORs only
            vector<Expression> operand_representations;
            for(int j = 0; j<operands.size();j++){
                operand_representations.push_back(*(operands[j])); // put all operand expressions into a set
            }
            for(int j = 0; j<operands.size();j++){
                if((Expression_type == Expression::AND && operands[j]->Expression_type == Expression::OR)||
                    (Expression_type == Expression::OR && operands[j]->Expression_type == Expression::AND)){
                    // if the inner expression type is the opposite of the outer expression type
                    for(int k = 0; k < operands[j]->operands.size(); k++){
                        if(find(operand_representations.begin(),
                         operand_representations.end(), *(operands[j]->operands[k])) != operand_representations.end()) {
                            *old_expression = *this;
                            // if any sub-operand matches one of our outer operands, we will absorb the whole operand
                            operands.erase(operands.begin()+j); 
                            j--; // decrement j so the outer for loop iteration does not break
                            accomplished_something = true;
                            break;
                        }
                    }
                }
            }
            if(operands.size() == 1){
                *this = *(operands[0]); // if we eliminated all but one of the operands, we can eliminate this level of the expression structure
            }
            if(accomplished_something){
                printTransformation(*old_expression, *this, Expression::inference_rules[i]);
                return true;
            }
        }
    }
    if(inference_rules[i]=="distribution_forward"){ // attempt to map (a^b)|c to (a|c)^(b|c)
        bool accomplished_something = false;
        if(Expression_type == Expression::AND || Expression_type == Expression::OR){
            vector<vector<Expression*> > outer_expressions; // old outer expressions *a^b* and *c*
            for(int j = 0; j<operands.size();j++){
                vector<Expression*> inner_expressions; // old inner expressions *a* and *b*
                if((Expression_type == Expression::AND && operands[j]->Expression_type == Expression::OR)||
                    (Expression_type == Expression::OR && operands[j]->Expression_type == Expression::AND)){
                    for(int k = 0; k < operands[j]->operands.size(); k++){
                        inner_expressions.push_back(operands[j]->operands[k]);
                        accomplished_something = true;
                    }

                }
                else{
                    inner_expressions.push_back(operands[j]);
                }
                outer_expressions.push_back(inner_expressions);
            }
            if(accomplished_something){
                Expression* new_outer_expression = new Expression(); 
                if(Expression_type == Expression::AND){
                    new_outer_expression->Expression_type = Expression::OR;
                }
                else{
                    new_outer_expression->Expression_type = Expression::AND;
                }
                vector<Expression*> new_inner_expressions; // *a|c* and *b|c*
                int max_index = 1;
                for(int j = 0; j < outer_expressions.size(); j++){
                    max_index *= outer_expressions[j].size();
                }
                for(int j = 0; j < max_index; j++){
                    Expression* new_inner_expression = new Expression();
                    if(Expression_type == Expression::AND){
                        new_inner_expression->Expression_type = Expression::AND;
                    }
                    else{
                        new_inner_expression->Expression_type = Expression::OR;
                    }      
                    for(int k = 0; k < outer_expressions.size(); k++){
                        int num_choices = outer_expressions[k].size();
                        int change_interval = 1;
                        for(int l = k+1; l < outer_expressions.size(); l++){
                            change_interval *= outer_expressions[l].size();
                        }
                        Expression* new_exp = new Expression();
                        *new_exp = *(outer_expressions[k][(int)(floor(j/change_interval))%num_choices]);
                        new_inner_expression->operands.push_back(new_exp);
                    }
                    new_inner_expressions.push_back(new_inner_expression);
                }
                for(int k = 0; k < new_inner_expressions.size(); k++){
                    new_outer_expression->operands.push_back(new_inner_expressions[k]);
                }
                printTransformation(*this, *new_outer_expression, Expression::inference_rules[i]);
                *this = *new_outer_expression;
                return true;
            }
        }
    }
    if(inference_rules[i]=="distribution_backwards"){
        if(Expression_type == Expression::AND || Expression_type == Expression::OR){ // this rule applies to ANDs and ORs only
            pair<int,int> operands_with_matches = getOperandsWithMatches();
            if(operands_with_matches.first != -1){
                vector<Expression> expressions_in_both_expressions;
                vector<Expression> expressions_not_in_both_expressions;
                for(int j = 0; j < operands[operands_with_matches.first]->operands.size(); j++){
                    expressions_not_in_both_expressions.push_back(*(operands[operands_with_matches.first]->operands[j]));
                }
                for(int j = 0; j < operands[operands_with_matches.second]->operands.size(); j++){
                    if(find(expressions_not_in_both_expressions.begin(), expressions_not_in_both_expressions.end(), 
                                *(operands[operands_with_matches.second]->operands[j])) != expressions_not_in_both_expressions.end()) { 
                        expressions_in_both_expressions.push_back(*(operands[operands_with_matches.second]->operands[j]));
                        expressions_not_in_both_expressions.erase(find(expressions_not_in_both_expressions.begin(), expressions_not_in_both_expressions.end(), 
                                *(operands[operands_with_matches.second]->operands[j])));
                    }
                }
                if(expressions_in_both_expressions.size()>0){
                    Expression* old_expression = new Expression();
                    *old_expression = *this;
                    Expression* new_outer_operand = new Expression();
                    if(Expression_type == Expression::AND){
                        new_outer_operand->Expression_type = Expression::OR;
                    }
                    if(Expression_type == Expression::OR){
                        new_outer_operand->Expression_type = Expression::AND;
                    }
                    Expression new_first_operand = *operands[operands_with_matches.first];
                    Expression new_second_operand = *operands[operands_with_matches.second];
                    operands.erase(operands.begin()+operands_with_matches.first);
                    if(operands_with_matches.first < operands_with_matches.second){
                        operands.erase(operands.begin()+operands_with_matches.second - 1);
                    }
                    else{
                        operands.erase(operands.begin()+operands_with_matches.second);   
                    }
                    bool first_operand_empty = false;
                    bool second_operand_empty = false;
                    for(int j = 0; j < expressions_in_both_expressions.size(); j++){
                        for(int k = 0; k < new_first_operand.operands.size(); k++){
                            if(*(new_first_operand.operands[k])==expressions_in_both_expressions[j]){
                                new_first_operand.operands.erase(new_first_operand.operands.begin()+k);
                                k--;
                            }
                        }
                        if(new_first_operand.operands.size()==0){
                            first_operand_empty = true;
                        }
                        if(new_first_operand.operands.size()==1){
                            new_first_operand = *(new_first_operand.operands[0]);
                        }

                        for(int k = 0; k < new_second_operand.operands.size(); k++){
                            if(*(new_second_operand.operands[k])==expressions_in_both_expressions[j]){
                                new_second_operand.operands.erase(new_second_operand.operands.begin()+k);
                                k--;
                            }
                        }
                        if(new_second_operand.operands.size()==0){
                            second_operand_empty = true;
                        }
                        if(new_second_operand.operands.size()==1){
                            new_second_operand = *(new_second_operand.operands[0]);
                        }
                        Expression* new_exp = new Expression;
                        *new_exp = expressions_in_both_expressions[j];
                        new_outer_operand->operands.push_back(new_exp);
                    }
                    Expression* new_inner_operand = new Expression();
                    new_inner_operand->Expression_type = Expression_type;
                    if(!first_operand_empty){
                        Expression* new_first_exp = new Expression();
                        *new_first_exp = new_first_operand;
                        new_inner_operand->operands.push_back(new_first_exp);
                    }
                    if(!second_operand_empty){
                        Expression* new_second_exp = new Expression();
                        *new_second_exp = new_second_operand;
                        new_inner_operand->operands.push_back(new_second_exp);
                    }
                    bool inner_operand_empty = false;
                    if(first_operand_empty && second_operand_empty){
                        inner_operand_empty = true;
                    }
                    else if(first_operand_empty || second_operand_empty){
                        *new_inner_operand = *(new_inner_operand->operands[0]); 
                    }
                    if(!inner_operand_empty){
                        new_outer_operand->operands.push_back(new_inner_operand);
                    }
                    if(new_outer_operand->operands.size() == 1){
                        *new_outer_operand = *(new_outer_operand->operands[0]); 
                    }
                    if(operands.size()>0){
                        operands.push_back(new_outer_operand);
                    }
                    else{
                        *this = *new_outer_operand;
                    }

                    printTransformation(*old_expression, *this, Expression::inference_rules[i]);
                    return true;
                }
                    // we found something, yay!
                    /*for(int j = 0; j < operands.size(); j++){
                        Expression* unique_expression_in_this_expression = new Expression();
                        *unique_expression_in_this_expression = *(operands[j]);
                        for(int k = 0; k < unique_expression_in_this_expression->operands.size(); k++){
                            if(find(expressions_in_every_expression.begin(), expressions_in_every_expression.end(), 
                            *(unique_expression_in_this_expression->operands[k])) != expressions_in_every_expression.end()) {     
                                unique_expression_in_this_expression->operands.erase(unique_expression_in_this_expression->operands.begin()+k); 
                                k--;
                            }
                        }
                        if(unique_expression_in_this_expression->operands.size()==1){
                            *unique_expression_in_this_expression = *(unique_expression_in_this_expression->operands[0]);
                        }
                        expressions_not_in_every_expression.push_back(*unique_expression_in_this_expression);
                    }
                    Expression* new_expression = new Expression();
                    if(Expression_type == Expression::OR){
                        new_expression->Expression_type = Expression::AND;
                    }
                    else{
                        new_expression->Expression_type = Expression::OR;
                    }
                    for(int j = 0; j < expressions_in_every_expression.size(); j++){
                        new_expression->operands.push_back(&(expressions_in_every_expression[j]));
                    }
                    Expression* new_inner_expression = new Expression();
                    new_inner_expression->Expression_type = Expression_type;
                    for(int j = 0; j < expressions_not_in_every_expression.size(); j++){
                        new_inner_expression->operands.push_back(&(expressions_not_in_every_expression[j]));
                    }
                    new_expression->operands.push_back(new_inner_expression);
                    printTransformation(*this, *new_expression, Expression::inference_rules[i]);
                    *this = *new_expression;
                    return true;
                }
                */
                /*for(int j = 0; j < operands.size(); j++){
                    if((Expression_type == Expression::AND && operands[j]->Expression_type == Expression::OR)||
                        (Expression_type == Expression::OR && operands[j]->Expression_type == Expression::AND)){     
                        if(expressions_in_every_expression.size() == 0){ // we just started looking
                            for(int k = 0; k < operands[j]->operands.size(); k++){
                                expressions_in_every_expression.push_back(*(operands[j]->operands[k]));
                            }
                        }
                        else{
                            vector<Expression> expressions_in_this_expression;
                            for(int k = 0; k < operands[j]->operands.size(); k++){
                                expressions_in_this_expression.push_back(*(operands[j]->operands[k]));
                            }
                            for(int k = 0; k < expressions_in_every_expression.size(); k++){
                                if(find(expressions_in_this_expression.begin(), expressions_in_this_expression.end(), 
                                expressions_in_every_expression[k]) == expressions_in_this_expression.end()) {                            
                                expressions_in_every_expression.erase(expressions_in_every_expression.begin()+k); 
                                k--;
                                }
                            }
                            if(expressions_in_every_expression.size() == 0){ // no dups
                                break;
                            }
                        }
                    }
                    else{
                        expressions_in_every_expression.clear(); // make sure we don't try to process this if there are any extraneous args
                        break;
                    }
                }
                if(expressions_in_every_expression.size()>0){
                    // we found something, yay!
                    for(int j = 0; j < operands.size(); j++){
                        Expression* unique_expression_in_this_expression = new Expression();
                        *unique_expression_in_this_expression = *(operands[j]);
                        for(int k = 0; k < unique_expression_in_this_expression->operands.size(); k++){
                            if(find(expressions_in_every_expression.begin(), expressions_in_every_expression.end(), 
                            *(unique_expression_in_this_expression->operands[k])) != expressions_in_every_expression.end()) {     
                                unique_expression_in_this_expression->operands.erase(unique_expression_in_this_expression->operands.begin()+k); 
                                k--;
                            }
                        }
                        if(unique_expression_in_this_expression->operands.size()==1){
                            *unique_expression_in_this_expression = *(unique_expression_in_this_expression->operands[0]);
                        }
                        expressions_not_in_every_expression.push_back(*unique_expression_in_this_expression);
                    }
                    Expression* new_expression = new Expression();
                    if(Expression_type == Expression::OR){
                        new_expression->Expression_type = Expression::AND;
                    }
                    else{
                        new_expression->Expression_type = Expression::OR;
                    }
                    for(int j = 0; j < expressions_in_every_expression.size(); j++){
                        new_expression->operands.push_back(&(expressions_in_every_expression[j]));
                    }
                    Expression* new_inner_expression = new Expression();
                    new_inner_expression->Expression_type = Expression_type;
                    for(int j = 0; j < expressions_not_in_every_expression.size(); j++){
                        new_inner_expression->operands.push_back(&(expressions_not_in_every_expression[j]));
                    }
                    new_expression->operands.push_back(new_inner_expression);
                    printTransformation(*this, *new_expression, Expression::inference_rules[i]);
                    *this = *new_expression;
                    return true;
                }
                */
            }
        }
        // find all expressions that are in all inner expressions
        // create new expression with remaining expressions from inner expressions and in_all expressions
    }
    if(inference_rules[i]=="reduction"){ //  P ∧ (¬P ∨ Q) <-> P ∧ Q
        bool accomplished_something = false;
        if(Expression_type == Expression::AND || Expression_type == Expression::OR){ // this rule applies to ANDs and ORs only
            vector<Expression> operand_representations;
            for(int j = 0; j<operands.size();j++){
                operand_representations.push_back(*(operands[j])); // put all operand expressions into a set
            }
            Expression* old_expression = new Expression();
            for(int j = 0; j<operands.size();j++){
                if((Expression_type == Expression::AND && operands[j]->Expression_type == Expression::OR)||
                    (Expression_type == Expression::OR && operands[j]->Expression_type == Expression::AND)){
                    // if the inner expression type is the opposite of the outer expression type
                    for(int k = 0; k < operands[j]->operands.size(); k++){ 
                        // check each operand in this expression to see if it matches an expression from our outer expression set
                        Expression* negation_wrapper = new Expression();
                        if(operands[j]->operands[k]->Expression_type!= Expression::NOT){
                            negation_wrapper->Expression_type = Expression::NOT;
                            negation_wrapper->operands.push_back(operands[j]->operands[k]);
                        }
                        else{
                            negation_wrapper = operands[j]->operands[k]->operands[0];
                        }
                        if(find(operand_representations.begin(), operand_representations.end(), 
                            *(negation_wrapper)) != operand_representations.end()) {                            
                            *old_expression = *this;
                            // if any sub-operand matches one of our outer operands, we will absorb the whole operand
                            operands[j]->operands.erase(operands[j]->operands.begin()+k);
                            if(operands[j]->operands.size() == 1){
                                *(operands[j]) = *(operands[j]->operands[0]);
                            } 
                            accomplished_something = true;
                            goto finished;
                        }
                    }
                }
            }
            finished:
            if(accomplished_something){
                printTransformation(*old_expression, *this, Expression::inference_rules[i]);
                return true;
            }
        }
    }
    return false;
}
void Expression::clean(){ // merges ANDs and ORs for commutivity
    for(int i = 0; i < operands.size(); i++){
        operands[i]->clean();
    }
    vector<Expression*> temporary_operand_list;
    if(Expression_type == Expression::AND || Expression_type == Expression::OR){
        for(int i = 0; i < operands.size(); i++){
            if(operands[i]->Expression_type == Expression_type){
                while(operands[i]->operands.size()>0){
                    temporary_operand_list.push_back(operands[i]->operands.front());
                    operands[i]->operands.erase(operands[i]->operands.begin());
                }
                operands.erase(operands.begin()+i);
                i--;
            }
        }
    }
    for(int i = 0; i < temporary_operand_list.size(); i++){
        operands.push_back(temporary_operand_list[i]);
    }
    if(Expression_type == Expression::AND || Expression_type == Expression::OR){
        if(operands.size()==1){
            *this = *(operands[0]);
        }
    }
}

pair<int,int> Expression::getOperandsWithMatches() const{ // returns the indicies of the operands whose operands are of the opposite junction andshare a term
    if(Expression_type==Expression::AND || Expression_type==Expression::OR){
        for(int i = 0; i < operands.size(); i++){
            if((Expression_type == Expression::AND && operands[i]->Expression_type == Expression::OR)||
                    (Expression_type == Expression::OR && operands[i]->Expression_type == Expression::AND)){
                for(int j = 0; j < operands[i]->operands.size(); j++){
                    for(int k = i+1; k < operands.size(); k++){
                        if((Expression_type == Expression::AND && operands[k]->Expression_type == Expression::OR)||
                    (Expression_type == Expression::OR && operands[k]->Expression_type == Expression::AND)){
                            for(int l = 0; l < operands[k]->operands.size(); l++){
                                if(*(operands[i]->operands[j]) == *(operands[k]->operands[l]) ){
                                    return make_pair(i,k);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    return make_pair(-1,-1);
}

/* String conversion functions */

string Expression::getExpressionMathematically() const{
    string retStr = "";
    if(!is_atomic_symbol()){
        if(Expression_type == Expression::NOT){
            retStr += "NOT(";
        }
        if(Expression_type == Expression::AND){
            retStr += "AND(";
        }
        if(Expression_type == Expression::OR){
            retStr += "OR(";
        }
        retStr += operands[0]->getExpressionMathematically();
        for(int i = 1; i < operands.size(); i++){
            retStr += "," + operands[i]->getExpressionMathematically();
        }
        retStr += ")";
    }
    else{
        retStr += symbol;
    }
    return retStr;
}
void Expression::printExpressionMathematically() const{
    cout << getExpressionMathematically() << "\\\\" << endl;
}
string Expression::getExpressionHumanReadable() const{
    string retStr = "";
    if(Expression_type == Expression::NOT){
        retStr += "\\lnot (";
        retStr += operands[0]->getExpressionHumanReadable();
        retStr += ")";
    }
    if(Expression_type == Expression::AND){
        retStr += "(";
        retStr += operands[0]->getExpressionHumanReadable();
        for(int i = 1; i<operands.size();i++){
            retStr += "\\wedge " + operands[i]->getExpressionHumanReadable();
        }
        retStr += ")";
    }
    if(Expression_type == Expression::OR){
        retStr += "(";
        retStr += operands[0]->getExpressionHumanReadable();
        for(int i = 1; i < operands.size(); i++){
            retStr += "\\vee " + operands[i]->getExpressionHumanReadable();
        }
        retStr += ")";
    }
    if(Expression_type == Expression::ATOMIC){
        if(is_contradiction()){
            retStr+= "\\bot";
        }
        else if(is_tautology()){
            retStr+= "\\top";
        }
        else{
            retStr += symbol;
        }
    }
    return retStr;
}
void Expression::printExpressionHumanReadable() const{
    cout <<getExpressionHumanReadable() << "\\\\" << endl;
}
void printTransformation(const Expression& from , const Expression& to , const string method){
    if(from.suppress_output){
        return;
    }
    //cout << "\\hfill$" << from.getExpressionHumanReadable() <<  "\\Leftrightarrow";
    //cout << to.getExpressionHumanReadable() << "$\\hfill By " << method << "\\\\" << endl;
    string method_cpy = method;
    std::replace(method_cpy.begin(), method_cpy.end(), '_', ' ');
    cout << "\\noindent \\textbox{\\hfill} \\textbox{\\hfil $ \\Downarrow $ \\hfil} \\textbox{\\hfill By "<< method_cpy << " }"  << endl;

}
