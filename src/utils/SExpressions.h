/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#ifndef SEXPRESSIONS_H
#define SEXPRESSIONS_H

#include <cassert>
#include <iostream>
#include <string>
#include <variant>
#include <vector>

struct SExpression {
    using args_t = std::vector<SExpression>;
    std::variant<std::string, args_t> data;

    [[nodiscard]] std::string toString() const;
};

inline bool isAtom(SExpression const & expr) {
    return std::holds_alternative<std::string>(expr.data);
}

inline std::string const & asAtom(SExpression const & expr) {
    assert(isAtom(expr));
    return std::get<std::string>(expr.data);
}

inline auto const & asSubExpressions(SExpression const & expr) {
    assert(!isAtom(expr));
    return std::get<SExpression::args_t>(expr.data);
}

inline auto & asSubExpressions(SExpression & expr) {
    assert(!isAtom(expr));
    return std::get<SExpression::args_t>(expr.data);
}

class SExpressionParser {
public:
    class ParsingException {};

    explicit SExpressionParser(std::istream & _input) : m_input(_input), m_token(static_cast<char>(m_input.get())) {}

    SExpression parseExpression();

    bool isEOF() {
        skipWhitespace();
        return m_input.eof();
    }

private:
    std::string parseToken();

    void skipWhitespace();

    [[nodiscard]] char token() const { return m_token; }

    void advance();

    std::istream & m_input;
    char m_token = 0;
};

#endif //SEXPRESSIONS_H
