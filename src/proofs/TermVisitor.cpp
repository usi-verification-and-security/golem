//
// Created by mambo on 8/15/23.
//
#include "Term.h"
#include <memory>
#include <string>

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

std::string OperateVisitor::visit(Op*term){
    std::string op = term->getOp();
    std::vector<std::shared_ptr<Term>> args = term->getArgs();
    PrintVisitor visitor;
    std::string firstStr;
    std::string secondStr;

    if (op == ">" or op == "<" or op == "<=" or op == ">="){
        firstStr = args[0]->accept(&visitor);
        secondStr = args[1]->accept(&visitor);
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), '('), firstStr.end());
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), ')'), firstStr.end());
        firstStr.erase(remove(firstStr.begin(), firstStr.end(), ' '), firstStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), '('), secondStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), ')'), secondStr.end());
        secondStr.erase(remove(secondStr.begin(), secondStr.end(), ' '), secondStr.end());
    }

    if (op == "="){
        if(args[0]->accept(&visitor) == args[1]->accept(&visitor)){
           return "true";
        }else{
           return "false";
        }
    }else if (op == ">"){
        if(stoi(firstStr) > stoi(secondStr)){
           return "true";
        }else{
           return "false";
        }
    }else if (op == "<"){
        if(stoi(firstStr) < stoi(secondStr)){
           return "true";
        }else{
           return "false";
        }
    }else if (op == "<="){
        if(stoi(firstStr) <= stoi(secondStr)){
           return "true";
        }else{
           return "false";
        }
    }else if (op == ">="){
        if(stoi(firstStr) >= stoi(secondStr)){
           return "true";
        }else{
           return "false";
        }
    }else if (op == "and"){
        int trues = 0;
        std::string fun;
        for (auto arg : args){
           if (arg->accept(&visitor) == "false"){
               return "false";
           }
           if (arg->accept(&visitor) == "true"){
               trues++;
           }
           if (arg->accept(&visitor) != "true"){
               fun = arg->accept(&visitor);
           }
        }
        if (trues == args.size()){
           return "true";
        }
        return fun;
    }else if (op == "or"){
        for (auto arg : args){
           if (arg->accept(&visitor) == "true"){
               return "true";
           }
        }
        return "false";
    }else if (op == "+"){
        int result = 0;
        for (auto arg : args) {
           std::string str = arg->accept(&visitor);
           str.erase(remove(str.begin(), str.end(), '('), str.end());
           str.erase(remove(str.begin(), str.end(), ')'), str.end());
           str.erase(remove(str.begin(), str.end(), ' '), str.end());
           result += std::stoi(str);
        }
        if (result < 0){
           return "(- " + std::to_string(result*(-1)) + ")";
        } else {
           return std::to_string(result);
        }
    }else if (op == "-"){
        std::string str = args[0]->accept(&visitor);
        str.erase(remove(str.begin(), str.end(), '('), str.end());
        str.erase(remove(str.begin(), str.end(), ')'), str.end());
        str.erase(remove(str.begin(), str.end(), ' '), str.end());
        int result = std::stoi(str);
        for (int i = 1; i < args.size(); i++) {
           str = args[i]->accept(&visitor);
           str.erase(remove(str.begin(), str.end(), '('), str.end());
           str.erase(remove(str.begin(), str.end(), ')'), str.end());
           str.erase(remove(str.begin(), str.end(), ' '), str.end());
           result -= std::stoi(str);
        }
        if (result < 0){
           return "(- " + std::to_string(result*(-1)) + ")";
        } else {
           return std::to_string(result);
        }
    }else if (op == "/"){
        std::string str = args[0]->accept(&visitor);
        str.erase(remove(str.begin(), str.end(), '('), str.end());
        str.erase(remove(str.begin(), str.end(), ')'), str.end());
        str.erase(remove(str.begin(), str.end(), ' '), str.end());
        int result = std::stoi(str);
        for (int i = 1; i < args.size(); i++) {
           str = args[i]->accept(&visitor);
           str.erase(remove(str.begin(), str.end(), '('), str.end());
           str.erase(remove(str.begin(), str.end(), ')'), str.end());
           str.erase(remove(str.begin(), str.end(), ' '), str.end());
           result /= std::stoi(str);
        }
        if (result < 0){
           return "(- " + std::to_string(result*(-1)) + ")";
        } else {
           return std::to_string(result);
        }
    }else if (op == "*"){
        std::string str = args[0]->accept(&visitor);
        str.erase(remove(str.begin(), str.end(), '('), str.end());
        str.erase(remove(str.begin(), str.end(), ')'), str.end());
        str.erase(remove(str.begin(), str.end(), ' '), str.end());
        int result = std::stoi(str);
        for (int i = 1; i < args.size(); i++) {
           str = args[i]->accept(&visitor);
           str.erase(remove(str.begin(), str.end(), '('), str.end());
           str.erase(remove(str.begin(), str.end(), ')'), str.end());
           str.erase(remove(str.begin(), str.end(), ' '), str.end());
           result *= std::stoi(str);
        }
        if (result < 0){
           return "(- " + std::to_string(result*(-1)) + ")";
        } else {
           return std::to_string(result);
        }
    }else if (op == "not"){
        if(args[0]->accept(&visitor) == "false"){
           return "true";
        }else{
           return "false";
        }
    } else if (op == "ite"){
        if (args[0]->accept(&visitor) == "true") {
           return args[1]->accept(&visitor);
        } else {
           return args[2]->accept(&visitor);
        }
    }
}

std::string OperateVisitor::visit(Let*term) {
    return "Error";
}

std::string SimplifyRuleVisitor::visit(Op* term) {
    std::string op = term->getOp();
    PrintVisitor printVisitor;
    auto args = term->getArgs();
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
    }else if (op == "/"){
        return "div_simplify";
    }else if (op == "*"){
        return "prod_simplify";
    }else if (op == "not"){
        return "not_simplify";
    } else if (op == "ite") {
        return "ite_simplify";
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
           return std::make_shared<Terminal>(pair.second, Term::INT);
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

std::shared_ptr<Term> ImplicationLHSVisitor::visit(Terminal* term){
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> ImplicationLHSVisitor::visit(Op* term){
    std::string opcode = term->getOp();
    if (opcode == "=>"){
        return term->getArgs()[0]->accept(this);
    }
    std::vector<std::shared_ptr<Term>> args;
    for (std::shared_ptr<Term> arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<Op>(opcode, args);
}

std::shared_ptr<Term> ImplicationLHSVisitor::visit(App* term){
    std::vector<std::shared_ptr<Term>> args;
    std::string fun = term->getFun();
    for (std::shared_ptr<Term> arg : term->getArgs()) {
        args.push_back(arg->accept(this));
    }
    return std::make_shared<App>(fun, args);
}

std::shared_ptr<Term> ImplicationLHSVisitor::visit(Quant* term){
    std::shared_ptr<Term> coreTerm = term->getCoreTerm()->accept(this);
    return coreTerm->accept(this);
}

std::shared_ptr<Term> ImplicationLHSVisitor::visit(Let* term){
    return std::make_shared<Let>(term->getTermNames(), term->getDeclarations(), term->getApplication());
}

std::shared_ptr<Term> SimplifyNonLinearVisitor::visit(Op* term){
    auto args = term->getArgs();
    auto op = term->getOp();
    std::vector<std::shared_ptr<Term>> newArgs;

    NonLinearVisitor nonLinearVisitor;

    for (auto arg : args) {
        if (arg->accept(&nonLinearVisitor)) {
           newArgs.push_back(arg);
        }
    }
    return std::make_shared<Op>(op, newArgs);
}

std::shared_ptr<Term> SimplifyLocatorVisitor::visit(Terminal* term){
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> SimplifyLocatorVisitor::visit(Op* term){
    bool simplification = true;
    std::vector<std::shared_ptr<Term>> args = term->getArgs();
    std::string op = term->getOp();
    TerminalOrAppVisitor visitor;

    for (std::shared_ptr<Term> arg : args){
        if (not arg->accept(&visitor)){
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
        if (not arg->accept(&visitor)){
           //if it is not, call the visit method on it
           std::shared_ptr<Term> possible = arg->accept(this);
           //check if it returned another terminal
           if (not possible->accept(&visitor)){
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
        return std::make_shared<Terminal>(simplification, Term::INT);
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
    return std::make_shared<Quant>(term->getQuant(), term->getVars(), term->getSorts(), term->getCoreTerm());
}

std::shared_ptr<Term> SimplifyLetTermVisitor::visit(Terminal* term){
    return std::make_shared<Terminal>(term->getVal(), term->getType());
}

std::shared_ptr<Term> SimplifyLetTermVisitor::visit(Op* term){

    auto args = term->getArgs();
    std::vector<std::shared_ptr<Term>> newArgs;
    auto op = term->getOp();

    for (auto arg : args){
        newArgs.push_back(arg->accept(this));
    }
    return std::make_shared<Op>(op, newArgs);
}

std::shared_ptr<Term> SimplifyLetTermVisitor::visit(App* term){
    return std::make_shared<App>(term->getFun(), term->getArgs());
}

std::shared_ptr<Term> SimplifyLetTermVisitor::visit(Quant* term){
    std::shared_ptr<Term> coreTerm = term->getCoreTerm()->accept(this);
    return std::make_shared<Quant>(term->getQuant(), term->getVars(), term->getSorts(), coreTerm);
}

std::shared_ptr<Term> SimplifyLetTermVisitor::visit(Let* term){

    if (letTerm == term) {
        return simplification;
    }
    return std::make_shared<Let>(term->getTermNames(), term->getDeclarations(), term->getApplication());
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

bool RequiresCongVisitor::visit(Op* term){
    TerminalOrAppVisitor terminalOrAppVisitor;
    for (auto arg : term->getArgs()) {
        if  (not arg->accept(&terminalOrAppVisitor)) {
             return true;
        }
    }
    return false;
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

bool NonLinearVisitor::visit(Op* term){

    auto op = term->getOp();
    auto args = term->getArgs();
    int predicates = 0;

    if (op == "=>"){
        return args[0]->accept(this);
    }

    if (op == "and" or op == "or") {

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
    TerminalOrAppVisitor visitor;
    PrintVisitor printVisitor;

    for (std::shared_ptr<Term> arg : args){
        if (not arg->accept(&visitor)){
           simplification = false;
        }
    }

    if (simplification and op != "=>") { return term; }

    for (std::shared_ptr<Term> arg : args){
        //check if it is a terminal
        if (not arg->accept(&visitor)){
           //if it is not, call the visit method on it
           Term* possible = arg->accept(this);
           //check if it returned another terminal
           if (not possible->accept(&visitor)){
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

