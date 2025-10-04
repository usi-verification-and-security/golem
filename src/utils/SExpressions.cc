/*
 * Copyright (c) 2025, Martin Blicha <martin.blicha@gmail.com>
 *
 * SPDX-License-Identifier: MIT
 */

#include "SExpressions.h"

#include <sstream>

std::string SExpression::toString() const {
    return std::visit(
        []<typename V>(V const & value) -> std::string {
            if constexpr (std::same_as<std::decay_t<V>, std::string>) {
                return value;
            } else if constexpr (std::same_as<std::decay_t<V>, args_t>) {
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
        },
        data);
}

SExpression SExpressionParser::parseExpression() {
    skipWhitespace();
    if (token() == '(') {
        advance();
        skipWhitespace();
        std::vector<SExpression> subExpressions;
        while (token() != 0 && token() != ')') {
            subExpressions.emplace_back(parseExpression());
            skipWhitespace();
        }
        if (token() != ')') throw ParsingException{};
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
} // namespace

std::string SExpressionParser::parseToken() {
    std::string result;

    skipWhitespace();
    bool isPipe = token() == '|';
    if (isPipe) advance();
    while (token() != 0) {
        char c = token();
        if (isPipe && c == '|') {
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
    if (!m_input.good()) throw ParsingException{};
    m_token = static_cast<char>(m_input.get());
    if (token() == ';')
        while (token() != '\n' && token() != 0)
            m_token = static_cast<char>(m_input.get());
}

void SExpressionParser::skipWhitespace() {
    while (isWhiteSpace(token()))
        advance();
}