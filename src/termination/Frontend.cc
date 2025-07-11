#include <cassert>
#include <string>
#include <sstream>
#include <unordered_map>
#include <variant>
#include <vector>


namespace golem::termination {

struct SExpression {
	using args_t = std::vector<SExpression>;
	std::variant<std::string, args_t> data;

	[[nodiscard]] std::string toString() const;
};

inline bool isAtom(SExpression const& expr)
{
	return std::holds_alternative<std::string>(expr.data);
}

inline std::string const& asAtom(SExpression const& expr)
{
	assert(isAtom(expr));
	return std::get<std::string>(expr.data);
}

inline auto const& asSubExpressions(SExpression const& expr)
{
	assert(!isAtom(expr));
	return std::get<SExpression::args_t>(expr.data);
}

inline auto& asSubExpressions(SExpression& expr)
{
	assert(!isAtom(expr));
	return std::get<SExpression::args_t>(expr.data);
}

class SExpressionParser {
public:
	class ParsingException {};

	explicit SExpressionParser(std::istream& _input) :
			m_input(_input),
			m_token(static_cast<char>(m_input.get())) {}

	SExpression parseExpression();

	bool isEOF()
	{
		skipWhitespace();
		return m_input.eof();
	}

private:
	std::string parseToken();

	void skipWhitespace();

	[[nodiscard]] char token() const
	{
		return m_token;
	}

	void advance();

	std::istream& m_input;
	char m_token = 0;
};

struct LocationDeclaration {
    std::string name;
    std::vector<std::string> argTypes;
};

struct Location {
    std::string name;
    std::vector<std::string> arguments;
};

struct Expr {
    enum Kind { And, Or, Eq, Add, Var, Const } kind;
    std::vector<std::shared_ptr<Expr>> children;
    std::string value;
};

struct Rule {
	Location lhs;
	Location rhs;
	std::shared_ptr<Expr> guard;
};

struct ITS {
	std::string format;
	std::string theory;
	std::unordered_map<std::string, LocationDeclaration> locations;
	std::string entrypoint;
	std::vector<Rule> rules;

	void resolve(SExpression const & topLevelDeclaration);
	LocationDeclaration parseFun(SExpression const &);
	Rule parseRule(SExpression const &);
};

ITS parseITS(std::istream & input) {
	ITS its;
	SExpressionParser parser(input);
	assert(not parser.isEOF());
	while (not parser.isEOF()) {
		auto expression = parser.parseExpression();
		its.resolve(expression);
	}
	return its;
}


/*
 *	Implementation
 */



std::string SExpression::toString() const {
	return std::visit([]<typename V>(V const & value) -> std::string {
		if constexpr (std::same_as<std::decay_t<V>, std::string>) { return value; }
		else if constexpr (std::same_as<std::decay_t<V>, args_t>) {
			std::stringstream result;
			result << '(';
			bool first = true;
			for (auto const & arg : value) {
				if (!first) result << ' ';
				result << arg.toString();
				first = false;
			}
			result << ")";
			return result.str();
		}
	}, data);
}

SExpression SExpressionParser::parseExpression() {
	skipWhitespace();
	if (token() == '(')
	{
		advance();
		skipWhitespace();
		std::vector<SExpression> subExpressions;
		while (token() != 0 && token() != ')')
		{
			subExpressions.emplace_back(parseExpression());
			skipWhitespace();
		}
		if (token() != ')')
			throw ParsingException{};
		// Simulate whitespace because we do not want to read the next token since it might block.
		m_token = ' ';
		return {std::move(subExpressions)};
	} else
		return {parseToken()};
}

namespace {
	bool isWhiteSpace(char c) {
		return c == ' ' || c == '\n' || c == '\t' || c == '\r';
	}
}

std::string SExpressionParser::parseToken() {
	std::string result;

	skipWhitespace();
	bool isPipe = token() == '|';
	if (isPipe)
		advance();
	while (token() != 0)
	{
		char c = token();
		if (isPipe && c == '|')
		{
			advance();
			break;
		} else if (!isPipe && (isWhiteSpace(c) || c == '(' || c == ')'))
			break;
		result.push_back(c);
		advance();
	}
	return result;
}

void SExpressionParser::advance() {
	if (!m_input.good())
		throw ParsingException{};
	m_token = static_cast<char>(m_input.get());
	if (token() == ';')
		while (token() != '\n' && token() != 0)
			m_token = static_cast<char>(m_input.get());
}

void SExpressionParser::skipWhitespace() {
	while (isWhiteSpace(token()))
		advance();
}

void ITS::resolve(SExpression const & topLevelDeclaration) {
	if (isAtom(topLevelDeclaration)) { throw SExpressionParser::ParsingException{}; }
	auto const & expressions = asSubExpressions(topLevelDeclaration);
	if (expressions.empty()) { throw SExpressionParser::ParsingException{}; }
	auto const & keyword = asAtom(expressions[0]);
	if (keyword == "format") {
		this->format = asAtom(expressions[1]);
	} else if (keyword == "theory") {
		this->theory = asAtom(expressions[1]);
	} else if (keyword == "fun") {
		auto declaration = parseFun(topLevelDeclaration);
		this->locations.insert({declaration.name, declaration});
	} else if (keyword == "entrypoint") {
		this->entrypoint = asAtom(expressions[1]);
	} else if (keyword == "rule") {
		this->rules.push_back(parseRule(topLevelDeclaration));
	} else {
		throw SExpressionParser::ParsingException{};
	}
}


} // namespace golem::termination
