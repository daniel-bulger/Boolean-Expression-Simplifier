#include <vector>
#include <set>
#include <utility>
#include <algorithm>
using namespace std;
struct ExpressionComparator;
class Expression{
public:

    /* class variables */

    static vector<string> inference_rules;
    static bool suppress_output; // controls whether the simplify() function writes to cout
    vector<Expression*> operands; // will hold the Expression's operand(s)
    char symbol; // this will be set if this Expression object represents an atomic statement
    enum Expression_types{
        OR, AND, NOT, IMPLICATION, BICONDITIONAL, ATOMIC
    };
    int Expression_type;

    /* Functions */

    Expression(){
        if (Expression::inference_rules.size() == 0) {
            Expression::inference_rules.push_back("eliminate_implication");
            Expression::inference_rules.push_back("double negation");
            Expression::inference_rules.push_back("identity");
            Expression::inference_rules.push_back("annihilation");
            Expression::inference_rules.push_back("contradiction");
            Expression::inference_rules.push_back("tautology");
            Expression::inference_rules.push_back("inverse");
            Expression::inference_rules.push_back("idepotence");
            Expression::inference_rules.push_back("demorgan");
            Expression::inference_rules.push_back("absorption");
            Expression::inference_rules.push_back("reduction");
            Expression::inference_rules.push_back("distribution_backwards");
            //Expression::inference_rules.push_back("distribution_forward");
            Expression::suppress_output = false;
        }
        Expression_type = ATOMIC;
        symbol = '\0'; // set the symbol to the null character initially
    }
    // Copy constructor
    Expression(const Expression& existingExpression)
    {
        operands.clear();
        for(int i = 0; i < existingExpression.operands.size(); i++){
            Expression* new_exp = new Expression();
            *new_exp = *(existingExpression.operands[i]);
            operands.push_back(new_exp);
        }
        symbol = existingExpression.symbol;
        Expression_type = existingExpression.Expression_type;
    }
 
    Expression& operator= (const Expression& existingExpression){
        operands.clear();
        for(int i = 0; i < existingExpression.operands.size(); i++){
            Expression* new_exp = new Expression();
            *new_exp = *(existingExpression.operands[i]);
            operands.push_back(new_exp);
        }
        symbol = existingExpression.symbol;
        Expression_type = existingExpression.Expression_type;
        return *this;
    }
    bool is_atomic_symbol() const
    {
        return (operands.size()==0);
    }
    void clean(); // merges connected ANDs and ORs for associativity efficiency -- a^(b^c) -> a^b^c
    void simplifyCompletely();
    bool simplify(); // attempts to simplify the function.  Returns true if function has changed
    bool applyInferenceRule(int n); // attempts to apply the nth defined inference rule.  Returns true if inference rule is applied
    bool directlyApplyInferenceRule(int i);
    pair<int,int> getOperandsWithMatches() const;
    string getExpressionHumanReadable() const;
    void printExpressionHumanReadable() const;
    string getExpressionMathematically() const;
    void printExpressionMathematically() const;
    bool is_tautology() const{ return(symbol == '1'); }
    bool is_contradiction() const{ return(symbol == '0'); }
    bool operator<(const Expression& other) const;
    bool operator>(const Expression& other){return !(*(this) < other);}
};
/*struct ExpressionComparator {
    inline bool operator()(const Expression* expr1, const Expression* expr2) const {
        return (*(expr1) < *(expr2));
    }
};*/

inline bool operator==(const Expression& lhs, const Expression& rhs)
{
    if(lhs.operands.size() != rhs.operands.size()){
        return false;
    }
    if(lhs.operands.size() == 0){
        return (lhs.symbol == rhs.symbol);
    }
    if(lhs.Expression_type != rhs.Expression_type){
        return false;
    }
    vector<Expression*> unused_rhs_ops = rhs.operands;
    bool has_match = false;
    for(int i = 0; i < lhs.operands.size(); i++){
        has_match = false;
        for(int j = 0; j < unused_rhs_ops.size(); j++){
            if(*(lhs.operands[i]) == *(unused_rhs_ops[j])){
                has_match = true;
                unused_rhs_ops.erase(unused_rhs_ops.begin()+j);
                j--;
            }
        }
        if(!has_match){
            return false;
        }
    }
    return true;
}
inline bool operator!=(const Expression& lhs, const Expression& rhs)
{
    return !(operator == (lhs,rhs));
}
