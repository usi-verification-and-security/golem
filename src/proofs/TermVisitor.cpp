//
// Created by mambo on 8/15/23.
//
#include "FastRational.h"
#include "Term.h"
#include <memory>
#include <string>
#include <cassert>

std::string PrintVisitor::visit(Terminal* term) {
    return term->getVal();
}

std::string PrintVisitor::visit(Op* term) {
    std::stringstream ss;
    ss << "(" << term->getOp();
    for (const std::shared_ptr<Term>& arg : term->getArgs()){
        ss << " " << arg->accept(this);
    }
    ss << ")";
    return ss.str();
}

std::string PrintVisitor::visit(App* term) {
    std::stringstream ss;
    ss << "(" << term->getFun();
    for (const std::shared_ptr<Term>& arg : term->getArgs()){
        ss << " " << arg->accept(this);
    }
    ss << ")";
    return ss.str();
}

std::string PrintVisitor::visit(Quant* term) {
    std::stringstream ss;
    ss << "(" << term->getQuant() << " (";
    for (int i = 0; i < term->getVars().size(); i++){
        ss << "(" << term->getVars()[i]->accept(this)
            << " " << term->getSorts()[i]->accept(this) << ")";
        if(i+1 != term->getVars().size()){
           ss << " ";
        }
    }
    ss << ")" << " " << term->getCoreTerm()->accept(this) << ")";
    return ss.str();
}

std::string PrintVisitor::visit(Let* term) {
    std::stringstream ss;
    auto names = term->getTermNames();
    ss << "(" << "let" << " (";
    for (int i = 0; i < names.size(); i++){
        ss << "(" << names[i]
           << " " << term->getDeclarations()[i]->accept(this) << ")";
        if(i+1 != names.size()){
           ss << " ";
        }
    }
    ss << ")" << " " << term->getApplication()->accept(this) << ")";
    return ss.str();
}

std::string Op::simplifyRule() {
    std::string op = operation;
    PrintVisitor printVisitor;
    if (op == "="){
        if ((args[0]->accept(&printVisitor).find_first_not_of("( )-0123456789") == std::string::npos) and (args[0]->accept(&printVisitor).find_first_not_of("( )-0123456789") == std::string::npos)){
           return "eq_simplify";
        } else {
           return "equiv_simplify";
        }
    }else if ((op == ">") or (op == "<") or (op == "<=") or (op == ">=")){
        return "comp_simplify";
    }else if (op == "and"){
        return "and_simplify";
    }else if (op == "or"){
        return "or_simplify";
    }else if (op == "+"){
        return "sum_simplify";
    }else if (op == "-"){
        return "minus_simplify";
    }else if (op == "/" or op == "div"){
        return "div_simplify";
    }else if (op == "*"){
        return "prod_simplify";
    }else if (op == "not"){
        return "not_simplify";
    } else if (op == "ite") {
        return "ite_simplify";
    } else if (op == "mod") {
        return "mod_simplify";
    }
    return "Error";
}

std::string NegatedAndVisitor::visit(Op* term) {
    std::stringstream ss;
    PrintVisitor printVisitor;
    auto op = term->getOp();
    auto args = term->getArgs();
    if (op == "and") {
        for (int i = 0; i < args.size(); i++) {
           ss << "(not " << args[i]->accept(&printVisitor) << ")";
           if (i != args.size()-1) {
               ss << " ";
           }
        }
        return ss.str();
    } else {
        return "Error";
    }
}

std::shared_ptr<Term> InstantiateVisitor::visit(Terminal* term){
    auto val = term->getVal();
    auto type = term->getType();
    if(type != Term::VAR) {return std::make_shared<Terminal>(val, type);}
    for (std::pair<std::string, std::string> pair : instPairs){
        if (val == pair.first){
           if (pair.second == "true" or pair.second == "false") {
               return std::make_shared<Terminal>(pair.second, Term::BOOL);
           } else if (pair.second.find('.') != std::string::npos) {
               return std::make_shared<Terminal>(pair.second, Term::REAL);
           } else {
               return std::make_shared<Terminal>(pair.second, Term::INT);
           }
        }
    }
    return std::make_shared<Terminal>(val, type);
}

std::shared_ptr<Term> InstantiateVisitor::visit(Op* term){
    std::vector<std::shared_ptr<Term>> args;
    std::string opcode = term->getOp();
    for (std::shared_ptr<Term> arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<Op>(opcode, args);
}

std::shared_ptr<Term> InstantiateVisitor::visit(App* term){
    std::vector<std::shared_ptr<Term>> args;
    std::string fun = term->getFun();
    for (std::shared_ptr<Term> arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<App>(fun, args);
}

std::shared_ptr<Term> InstantiateVisitor::visit(Quant* term){
    std::shared_ptr<Term> coreTerm = term->getCoreTerm()->accept(this);
    return coreTerm;
}

std::shared_ptr<Term> InstantiateVisitor::visit(Let* term){
    std::vector<std::shared_ptr<Term>> declarations;
    auto application = term->getApplication();
    for (std::shared_ptr<Term> dec : term->getDeclarations()) {
        declarations.push_back(dec->accept(this));
    }
    application->accept(this);
    return std::make_shared<Let>(term->getTermNames(), declarations, application);
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(Quant* term) {

    //one pass colection
    auto vars = term->getVars();
    auto sorts = term->getSorts();
    auto coreTerm = term->getCoreTerm();
    bool inUse = false;
    PrintVisitor printVisitor;

    coreTerm->accept(this);

    for (int i = 0; i < vars.size(); i++) {
        auto var = vars[i];
        for (auto varInUse : varsInUse) {
           if (var->accept(&printVisitor) == varInUse){
               inUse = true;
           }
        }
        if (!inUse) {
           vars.erase(vars.begin()+i);
           sorts.erase(sorts.begin()+i);
        }
        inUse = false;
    }

    if (vars.empty()) {
        return term->getCoreTerm();
    }
    return std::make_shared<Quant>(term->getQuant(), vars, sorts, term->getCoreTerm());
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(Terminal* term) {
    PrintVisitor printVisitor;
    for (auto var : varsInUse) {
        if (term->accept(&printVisitor) == var){
           return nullptr;
        }
    }
    varsInUse.push_back(term->accept(&printVisitor));
    return nullptr;
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(Op* term) {
    auto args = term->getArgs();
    for (auto arg : args) {
        arg->accept(this);
    }
    return nullptr;
}

std::shared_ptr<Term> RemoveUnusedVisitor::visit(App* term) {
    auto args = term->getArgs();
    for (auto arg : args) {
        arg->accept(this);
    }
    return nullptr;
}

std::shared_ptr<Term> SimplifyLocatorVisitor::visit(Terminal* term){
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> SimplifyLocatorVisitor::visit(Op* term){
    bool simplification = true;
    std::vector<std::shared_ptr<Term>> args = term->getArgs();
    std::string op = term->getOp();

    for (std::shared_ptr<Term> arg : args){
        if (not (arg->getTermType() == Term::TERMINAL or arg->getTermType() == Term::APP)){
           simplification = false;
        }
    }

    if (simplification and op != "=>"){
        std::vector<std::shared_ptr<Term>> newArgs;
        for (std::shared_ptr<Term> arg : args){
           std::shared_ptr<Term> newArg = arg->accept(this);
           newArgs.push_back(newArg);
        }
        return std::make_shared<Op>(term->getOp(), newArgs);
    }

    for (std::shared_ptr<Term> arg : args){
        //check if it is a terminal
        if (not (arg->getTermType() == Term::TERMINAL or arg->getTermType() == Term::APP)){
           //if it is not, call the visit method on it
           std::shared_ptr<Term> possible = arg->accept(this);
           //check if it returned another terminal
           if (not (possible->getTermType() == Term::TERMINAL or possible->getTermType() == Term::APP)){
               return possible;
           }
        }
    }

    return std::make_shared<Terminal>("No Possible Simplification", Term::UNDECLARED);

}

std::shared_ptr<Term> SimplifyLocatorVisitor::visit(App* term){
    return std::make_shared<App>(term->getFun(), term->getArgs());
}

std::shared_ptr<Term> SimplifyLocatorVisitor::visit(Quant* term){
    return term->getCoreTerm()->accept(this);
}

std::shared_ptr<Term> SimplifyLocatorVisitor::visit(Let* term){
    return std::make_shared<Let>(term->getTermNames(), term->getDeclarations(), term->getApplication());
}

std::shared_ptr<Term> SimplifyVisitor::visit(Terminal* term){
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> SimplifyVisitor::visit(Op* term){

    auto args = term->getArgs();
    std::vector<std::shared_ptr<Term>> newArgs;
    auto op = term->getOp();

    if (operation == term){
        return simplification;
    } else {
        for (auto arg : args){
           newArgs.push_back(arg->accept(this));
        }
        return std::make_shared<Op>(op, newArgs);
    }
}

std::shared_ptr<Term> SimplifyVisitor::visit(App* term){
    return std::make_shared<App>(term->getFun(), term->getArgs());
}

std::shared_ptr<Term> SimplifyVisitor::visit(Quant* term){

    return std::make_shared<Quant>(term->getQuant(), term->getVars(), term->getSorts(), term->getCoreTerm()->accept(this));
}

std::shared_ptr<Term> SimplifyVisitor::visit(Let* term){

    if (operation == term) {
        return simplification;
    }
    return std::make_shared<Let>(term->getTermNames(), term->getDeclarations(), term->getApplication());
}

std::shared_ptr<Term> OperateVisitor::visit(Op* term){
    std::string op = term->getOp();
    std::vector<std::shared_ptr<Term>> args = term->getArgs();
    std::vector<std::shared_ptr<Term>> newArgs;
    PrintVisitor visitor;
    InstantiateVisitor fakeInstantiation;
    std::string firstStr;
    std::string secondStr;
    FastRational firstTerm;
    FastRational secondTerm;

    if (op == "<" or op == "<=" or op == "-" or op == "*" or op == "/" or op == "mod" or op == "div"){
        assert(args[0]->getTerminalType() != Term::VAR);
        assert(args[1]->getTerminalType() != Term::VAR);
        firstStr = args[0]->accept(&visitor);
        secondStr = args[1]->accept(&visitor);
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), '('), firstStr.end());
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), ')'), firstStr.end());
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), ' '), firstStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), '('), secondStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), ')'), secondStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), ' '), secondStr.end());
        firstTerm = FastRational(&firstStr[0], 10);
        secondTerm = FastRational(&secondStr[0], 10);
    }

    if (op == "="){
        assert(args[0]->getTerminalType() != Term::VAR);
        assert(args[1]->getTerminalType() != Term::VAR);
        if(args[0]->accept(&visitor) == args[1]->accept(&visitor)){
           return std::make_shared<Terminal>("true", Term::BOOL);
        }else{
           return std::make_shared<Terminal>("false", Term::BOOL);
        }
    }else if (op == ">"){
        return std::make_shared<Op>("not", std::vector<std::shared_ptr<Term>>{std::make_shared<Op>("<=", args)});
    }else if (op == "<"){
        if(firstTerm < secondTerm){
           return std::make_shared<Terminal>("true", Term::BOOL);
        }else{
           return std::make_shared<Terminal>("false", Term::BOOL);
        }
    }else if (op == "<="){
        if(firstTerm <= secondTerm){
           return std::make_shared<Terminal>("true", Term::BOOL);
        }else{
           return std::make_shared<Terminal>("false", Term::BOOL);
        }
    }else if (op == ">="){
        newArgs.push_back(args[1]);
        newArgs.push_back(args[0]);
        return std::make_shared<Op>("<=", newArgs);
    }else if (op == "and"){
        int trues = 0;
        std::vector<std::shared_ptr<Term>> predicates;

        for (auto arg : args){
//           assert(arg->getTerminalType() != Term::VAR);
           if (arg->accept(&visitor) == "false"){
               return std::make_shared<Terminal>("false", Term::BOOL);
           }
           if (arg->accept(&visitor) == "true"){
               trues++;
           }
           if (arg->accept(&visitor) != "true"){
               predicates.push_back(arg);
           }
        }
        if (trues == args.size()){
           return std::make_shared<Terminal>("true", Term::BOOL);
        }
        if (predicates.size() == 1) {
           return predicates[0]->accept(&fakeInstantiation);
        } else {
            for (auto predicate : predicates) {
               newArgs.push_back(predicate->accept(&fakeInstantiation));
            }
            return std::make_shared<Op>("and", newArgs);
        }
    }else if (op == "or"){
        for (auto arg : args){
            assert(arg->getTerminalType() != Term::VAR);
            if (arg->accept(&visitor) == "true"){
               return std::make_shared<Terminal>("true", Term::BOOL);
            }
        }
        return std::make_shared<Terminal>("false", Term::BOOL);
    }else if (op == "+"){
        FastRational result = 0;
        for (auto arg : args) {
            assert(arg->getTerminalType() != Term::VAR);
            std::string str = arg->accept(&visitor);
            str.erase(remove(str.begin(), str.end(), '('), str.end());
            str.erase(remove(str.begin(), str.end(), ')'), str.end());
            str.erase(remove(str.begin(), str.end(), ' '), str.end());
            const char* ptr = &str[0];
            FastRational temp(ptr, 10);
            result += temp;
        }
        if (result < 0){
            result*=-1;
            return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
            return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    }else if (op == "-"){
        FastRational result = firstTerm - secondTerm;
        if (result < 0){
           result*=-1;
           return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
           return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    }else if (op == "/"){
        FastRational result = firstTerm / secondTerm;
        if (result < 0){
           result*=-1;
           return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
           return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    }else if (op == "*"){
        FastRational result = firstTerm * secondTerm;
        if (result < 0){
           result*=-1;
           return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
           return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    }else if (op == "not"){
        assert(args[0]->getTerminalType() != Term::VAR);
        if(args[0]->accept(&visitor) == "false"){
           return std::make_shared<Terminal>("true", Term::BOOL);
        }else{
           return std::make_shared<Terminal>("false", Term::BOOL);
        }
    } else if (op == "ite"){
        assert(args[0]->getTerminalType() != Term::VAR);
        assert(args[1]->getTerminalType() != Term::VAR);
        assert(args[2]->getTerminalType() != Term::VAR);
        if (args[0]->accept(&visitor) == "true") {
           return args[1]->accept(&fakeInstantiation);
        } else {
           return args[2]->accept(&fakeInstantiation);
        }
    } else if (op == "mod") {
        FastRational result = firstTerm % secondTerm;
        if (result < 0){
           result*=-1;
           return std::make_shared<Terminal>("(- " + result.get_str() + ")", Term::INT);
        } else {
           return std::make_shared<Terminal>(result.get_str(), Term::INT);
        }
    } else if (op == "div") {
        FastRational result = firstTerm / secondTerm;
        if (result < 0){
           result*=-1;
           return std::make_shared<Terminal>("(- " + result.ceil().get_str() + ")", Term::INT);
        } else {
           return std::make_shared<Terminal>(result.floor().get_str(), Term::INT);
        }
    }
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Terminal* term){

    for (int i = 0; i < terms.size(); i++) {
        if (term->getVal() == terms[i]) {
           return substitutions[i];
        }
    }
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Op* term){
    std::vector<std::shared_ptr<Term>> args;
    std::string opcode = term->getOp();
    for (std::shared_ptr<Term> arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<Op>(opcode, args);
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(App* term){
    std::vector<std::shared_ptr<Term>> args;
    std::string fun = term->getFun();
    for (std::shared_ptr<Term> arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<App>(fun, args);
}

std::shared_ptr<Term> OperateLetTermVisitor::visit(Let* term){
    terms = term->getTermNames();
    substitutions = term->getDeclarations();
    return term->getApplication()->accept(this);
}

Term* GetLocalParentBranchVisitor::visit(Op* term){
    auto args = term->getArgs();
    std::vector<std::shared_ptr<Term>> newArgs;
    auto op = term->getOp();

    if (op == "=>"){
        return args[0]->accept(this);
    }

    PrintVisitor printVisitor;

    for (auto arg : args) {
        if (operation == arg.get()){
            return term;
        } else if (arg->accept(&printVisitor).find(operation->accept(&printVisitor)) != std::string::npos) {
             Term* potential = arg->accept(this);
             if (potential != nullptr) {
               return potential;
             }
        }
    }

    return nullptr;
}

bool IsPrimaryBranchVisitor::visit(Op* term){
    PrintVisitor printVisitor;
    auto args = term->getArgs();

    if (term->getOp() == "=>"){
        if (branch == args[0].get()) {
             return true;
        } else {
             return args[0]->accept(this);
        }
    }

    for (auto arg : args) {
        if (branch == arg.get()){
           return true;
        }
    }

    return false;
}

bool NonLinearVisitor::visit(Terminal* term){
    if (term->getType() == Term::VAR) {
        return true;
    }
    else {
        return false;
    }
}

bool NonLinearVisitor::visit(Op* term){

    auto op = term->getOp();
    auto args = term->getArgs();
    int predicates = 0;

    if (op == "=>"){
        return args[0]->accept(this);
    }

    if (op == "and") {

        for (auto arg : args) {
           if (arg->accept(this)){
               predicates++;
           }
        }
        if (predicates >= 2) {
           return true;
        } else {
           return false;
        }
    } else {
        return false;
    }
}

Term* SimplifyHelperVisitor::visit(Terminal* term) {
    return term;
}

Term* SimplifyHelperVisitor::visit(Op* term) {
    bool simplification = true;
    std::vector<std::shared_ptr<Term>> args = term->getArgs();
    std::string op = term->getOp();
    PrintVisitor printVisitor;

    for (std::shared_ptr<Term> arg : args){
        if (not (arg->getTermType() == Term::TERMINAL or arg->getTermType() == Term::APP)){
           simplification = false;
        }
    }

    if (simplification and op != "=>") { return term; }

    for (std::shared_ptr<Term> arg : args){
        //check if it is a terminal
        if (not (arg->getTermType() == Term::TERMINAL or arg->getTermType() == Term::APP)){
           //if it is not, call the visit method on it
           Term* possible = arg->accept(this);
           //check if it returned another terminal
           if (not (possible->getTermType() == Term::TERMINAL or possible->getTermType() == Term::APP)){
               return possible;
           }
        }
    }

    std::make_shared<Terminal>("No Possible Simplification", Term::UNDECLARED).get();

}

Term* SimplifyHelperVisitor::visit(Let * term) {
    return term;
}

Term* SimplifyHelperVisitor::visit(App* term) {
    return term;
}

Term* SimplifyHelperVisitor::visit(Quant* term) {
    return term;
}

Term* LetLocatorVisitor::visit(Quant* term) {
    return term->getCoreTerm()->accept(this);
}

Term* LetLocatorVisitor::visit(Op* term) {
    auto args = term->getArgs();
    for (auto arg : args) {
        if (arg->accept(this) != nullptr) {
           return arg->accept(this);
        }
    }
    return nullptr;
}

Term* LetLocatorVisitor::visit(Let* term) {
    return term;
}

std::string Terminal::accept(StringVisitor* visitor) {
    return visitor->visit(this);
}

std::string Op::accept(StringVisitor* visitor) {
    return visitor->visit(this);
}

std::string App::accept(StringVisitor* visitor) {
    return visitor->visit(this);
}

std::string Quant::accept(StringVisitor* visitor) {
    return visitor->visit(this);
}

std::string Let::accept(StringVisitor* visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> Terminal::accept(LogicVisitor* visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> Op::accept(LogicVisitor* visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> App::accept(LogicVisitor* visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> Quant::accept(LogicVisitor* visitor) {
    return visitor->visit(this);
}

std::shared_ptr<Term> Let::accept(LogicVisitor* visitor) {
    return visitor->visit(this);
}

bool Terminal::accept(BooleanVisitor* visitor){
    return visitor->visit(this);
}

bool Op::accept(BooleanVisitor* visitor){
    return visitor->visit(this);
}

bool App::accept(BooleanVisitor* visitor){
    return visitor->visit(this);
}

bool Quant::accept(BooleanVisitor* visitor){
    return visitor->visit(this);
}

bool Let::accept(BooleanVisitor* visitor){
    return visitor->visit(this);
}

Term* Terminal::accept(PointerVisitor* visitor){
    return visitor->visit(this);
}

Term* Op::accept(PointerVisitor* visitor){
    return visitor->visit(this);
}

Term* App::accept(PointerVisitor* visitor){
    return visitor->visit(this);
}

Term* Quant::accept(PointerVisitor* visitor){
    return visitor->visit(this);
}

Term* Let::accept(PointerVisitor* visitor){
    return visitor->visit(this);
}

