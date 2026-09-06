/*
 * Luatrix / LTRIX native amalgamation
 *
 * This file is the dependency-free C++17 implementation of the Clyde
 * pipeline.  It intentionally has the same public shape as the native
 * deliverable requested by Luatrix:
 *
 *     luatrix <input> <out>
 *
 * The implementation keeps the source-preserving behavior of Clyde's
 * obfuscator, while also carrying a structured parser, stack/register
 * bytecode model, randomized opcode metadata, compression, and a generated
 * Lua-compatible bootstrap in one translation unit.  The original Clyde
 * TypeScript modules in vendor/clyde/src are the behavioral reference.
 */

#include <algorithm>
#include <array>
#include <cctype>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace luatrix {

struct Position {
    unsigned line = 1;
    unsigned column = 1;
};

struct Diagnostic {
    std::string message;
    Position at;
};

struct Token {
    enum class Kind { Word, Number, String, Comment, Space, Punct };
    Kind kind = Kind::Punct;
    std::string text;
    std::size_t offset = 0;
    Position at;
};

static bool is_word_start(char c) {
    return std::isalpha(static_cast<unsigned char>(c)) != 0 || c == '_';
}

static bool is_word_char(char c) {
    return std::isalnum(static_cast<unsigned char>(c)) != 0 || c == '_';
}

static bool trivia(const Token& token) {
    return token.kind == Token::Kind::Space || token.kind == Token::Kind::Comment;
}

static bool keyword(const std::string& value) {
    static const std::unordered_set<std::string> words = {
        "and", "break", "continue", "do", "else", "elseif", "end", "export",
        "false", "for", "function", "if", "in", "local", "nil", "not", "or",
        "repeat", "return", "then", "true", "type", "until", "while", "self",
        "declare", "read", "write"
    };
    return words.find(value) != words.end();
}

static std::size_t long_string_end(const std::string& source, std::size_t start) {
    if (start >= source.size() || source[start] != '[') {
        return std::string::npos;
    }
    std::size_t cursor = start + 1;
    while (cursor < source.size() && source[cursor] == '=') {
        ++cursor;
    }
    if (cursor >= source.size() || source[cursor] != '[') {
        return std::string::npos;
    }
    const std::string close = "]" + std::string(cursor - start - 1, '=') + "]";
    const std::size_t end = source.find(close, cursor + 1);
    return end == std::string::npos ? source.size() : end + close.size();
}

static std::vector<Token> lex(const std::string& source) {
    static const std::array<const char*, 22> operators = {
        "...", "//=", "..=", "==", "~=", "<=", ">=", "//", "..", "+=",
        "-=", "*=", "/=", "%=", "^=", "::", "->", "<<", ">>", "&=", "|=",
        "?"
    };
    std::vector<Token> tokens;
    Position position;
    std::size_t cursor = 0;

    auto advance = [&](std::size_t count) {
        for (std::size_t i = 0; i < count && cursor < source.size(); ++i, ++cursor) {
            if (source[cursor] == '\n') {
                ++position.line;
                position.column = 1;
            } else {
                ++position.column;
            }
        }
    };

    while (cursor < source.size()) {
        const std::size_t begin = cursor;
        const Position at = position;
        const char current = source[cursor];

        if (std::isspace(static_cast<unsigned char>(current)) != 0) {
            while (cursor < source.size() &&
                   std::isspace(static_cast<unsigned char>(source[cursor])) != 0) {
                advance(1);
            }
            tokens.push_back({Token::Kind::Space, source.substr(begin, cursor - begin), begin, at});
            continue;
        }

        if (current == '-' && cursor + 1 < source.size() && source[cursor + 1] == '-') {
            const std::size_t long_end = long_string_end(source, cursor + 2);
            if (cursor + 2 < source.size() && source[cursor + 2] == '[' &&
                long_end != std::string::npos) {
                advance(long_end - cursor);
            } else {
                while (cursor < source.size() && source[cursor] != '\n') {
                    advance(1);
                }
            }
            tokens.push_back({Token::Kind::Comment, source.substr(begin, cursor - begin), begin, at});
            continue;
        }

        if (current == '"' || current == '\'' || current == '`') {
            const char quote = current;
            advance(1);
            bool closed = false;
            while (cursor < source.size()) {
                if (source[cursor] == '\\') {
                    advance(std::min<std::size_t>(2, source.size() - cursor));
                } else {
                    const char c = source[cursor];
                    advance(1);
                    if (c == quote) {
                        closed = true;
                        break;
                    }
                }
            }
            (void)closed;
            tokens.push_back({Token::Kind::String, source.substr(begin, cursor - begin), begin, at});
            continue;
        }

        if (current == '[') {
            const std::size_t end = long_string_end(source, cursor);
            if (end != std::string::npos) {
                advance(end - cursor);
                tokens.push_back({Token::Kind::String, source.substr(begin, cursor - begin), begin, at});
                continue;
            }
        }

        if (is_word_start(current)) {
            advance(1);
            while (cursor < source.size() && is_word_char(source[cursor])) {
                advance(1);
            }
            tokens.push_back({Token::Kind::Word, source.substr(begin, cursor - begin), begin, at});
            continue;
        }

        if (std::isdigit(static_cast<unsigned char>(current)) != 0 ||
            (current == '.' && cursor + 1 < source.size() &&
             std::isdigit(static_cast<unsigned char>(source[cursor + 1])) != 0)) {
            advance(1);
            while (cursor < source.size()) {
                const char c = source[cursor];
                if (std::isalnum(static_cast<unsigned char>(c)) == 0 &&
                    c != '.' && c != '_') {
                    break;
                }
                advance(1);
            }
            tokens.push_back({Token::Kind::Number, source.substr(begin, cursor - begin), begin, at});
            continue;
        }

        bool found_operator = false;
        for (const char* op : operators) {
            const std::size_t length = std::char_traits<char>::length(op);
            if (source.compare(cursor, length, op) == 0) {
                advance(length);
                tokens.push_back({Token::Kind::Punct, source.substr(begin, length), begin, at});
                found_operator = true;
                break;
            }
        }
        if (!found_operator) {
            advance(1);
            tokens.push_back({Token::Kind::Punct, source.substr(begin, 1), begin, at});
        }
    }
    return tokens;
}

static std::pair<std::vector<Token>, std::vector<Diagnostic>>
lex_checked(const std::string& source) {
    std::vector<Token> tokens = lex(source);
    std::vector<Diagnostic> diagnostics;
    std::vector<std::string> delimiters;
    for (const Token& token : tokens) {
        if (token.kind == Token::Kind::String && token.text.size() >= 2 &&
            (token.text.front() == '"' || token.text.front() == '\'' ||
             token.text.front() == '`') &&
            token.text.back() != token.text.front()) {
            diagnostics.push_back({"unterminated string", token.at});
        }
        if (trivia(token) || token.kind == Token::Kind::String) {
            continue;
        }
        if (token.text == "(" || token.text == "[" || token.text == "{") {
            delimiters.push_back(token.text);
        } else if (token.text == ")" || token.text == "]" || token.text == "}") {
            const std::string expected = token.text == ")" ? "(" :
                                         (token.text == "]" ? "[" : "{");
            if (delimiters.empty() || delimiters.back() != expected) {
                diagnostics.push_back({"mismatched delimiter", token.at});
            } else {
                delimiters.pop_back();
            }
        }
    }
    if (!delimiters.empty()) {
        diagnostics.push_back({"unclosed delimiter", {1, 1}});
    }
    return {std::move(tokens), std::move(diagnostics)};
}

static std::string join_tokens(const std::vector<Token>& tokens) {
    std::string output;
    for (const Token& token : tokens) {
        output += token.text;
    }
    return output;
}

struct Expr {
    enum class Kind {
        Name, Literal, Unary, Binary, Call, Index, Member, Function, Table, Opaque
    };
    Kind kind = Kind::Opaque;
    std::string text;
    std::vector<Expr> children;
    std::vector<std::string> names;
    std::vector<struct Stmt> body;
};

struct Stmt {
    enum class Kind {
        Local, Assign, Return, Break, Continue, If, While, Repeat, For,
        Function, Call, Block, Type, Opaque
    };
    Kind kind = Kind::Opaque;
    std::string name;
    std::vector<std::string> names;
    std::vector<Expr> values;
    std::vector<Stmt> body;
    std::vector<Stmt> otherwise;
};

struct Chunk {
    std::vector<Stmt> body;
};

class Parser {
public:
    explicit Parser(const std::vector<Token>& tokens) : tokens_(tokens) {}

    Chunk parse() {
        return parse_block({});
    }

private:
    const std::vector<Token>& tokens_;
    std::size_t cursor_ = 0;

    void skip() {
        while (cursor_ < tokens_.size() && trivia(tokens_[cursor_])) {
            ++cursor_;
        }
    }

    std::string peek() {
        skip();
        return cursor_ < tokens_.size() ? tokens_[cursor_].text : std::string();
    }

    bool take(const std::string& text) {
        skip();
        if (cursor_ < tokens_.size() && tokens_[cursor_].text == text) {
            ++cursor_;
            return true;
        }
        return false;
    }

    static bool terminator(const std::string& value,
                           const std::unordered_set<std::string>& stops) {
        return stops.find(value) != stops.end();
    }

    Expr parse_primary() {
        skip();
        if (cursor_ >= tokens_.size()) {
            return {};
        }
        const std::string token = tokens_[cursor_].text;
        if (token == "(") {
            ++cursor_;
            Expr value = parse_expression(0);
            take(")");
            value.kind = Expr::Kind::Opaque;
            return parse_suffix(std::move(value));
        }
        if (token == "{") {
            ++cursor_;
            int depth = 1;
            Expr table;
            table.kind = Expr::Kind::Table;
            while (cursor_ < tokens_.size() && depth > 0) {
                const std::string current = tokens_[cursor_].text;
                if (current == "{") {
                    ++depth;
                } else if (current == "}") {
                    --depth;
                    if (depth == 0) {
                        ++cursor_;
                        break;
                    }
                }
                if (depth > 0) {
                    table.children.push_back(parse_expression(0));
                    if (peek() == ",") {
                        ++cursor_;
                    } else if (peek() != "}") {
                        ++cursor_;
                    }
                }
            }
            return parse_suffix(std::move(table));
        }
        if (token == "function") {
            ++cursor_;
            Expr function;
            function.kind = Expr::Kind::Function;
            if (take("(")) {
                while (cursor_ < tokens_.size() && peek() != ")") {
                    skip();
                    if (cursor_ < tokens_.size()) {
                        function.names.push_back(tokens_[cursor_].text);
                        ++cursor_;
                    }
                    if (!take(",")) {
                        break;
                    }
                }
                take(")");
            }
            function.body = parse_block({"end"}).body;
            take("end");
            return parse_suffix(std::move(function));
        }
        ++cursor_;
        Expr value;
        value.kind = (tokens_[cursor_ - 1].kind == Token::Kind::Word)
                         ? Expr::Kind::Name : Expr::Kind::Literal;
        value.text = token;
        if (token == "...") {
            value.kind = Expr::Kind::Opaque;
        }
        return parse_suffix(std::move(value));
    }

    Expr parse_suffix(Expr value) {
        while (true) {
            if (take("(")) {
                Expr call;
                call.kind = Expr::Kind::Call;
                call.children.push_back(std::move(value));
                while (cursor_ < tokens_.size() && peek() != ")") {
                    call.children.push_back(parse_expression(0));
                    if (!take(",")) {
                        break;
                    }
                }
                take(")");
                value = std::move(call);
            } else if (take("[")) {
                Expr index;
                index.kind = Expr::Kind::Index;
                index.children.push_back(std::move(value));
                index.children.push_back(parse_expression(0));
                take("]");
                value = std::move(index);
            } else if (take(".")) {
                Expr member;
                member.kind = Expr::Kind::Member;
                member.children.push_back(std::move(value));
                skip();
                if (cursor_ < tokens_.size()) {
                    member.text = tokens_[cursor_++].text;
                }
                value = std::move(member);
            } else {
                break;
            }
        }
        return value;
    }

    static int precedence(const std::string& op) {
        if (op == "or") return 1;
        if (op == "and") return 2;
        if (op == "==" || op == "~=" || op == "<" || op == ">" ||
            op == "<=" || op == ">=") return 3;
        if (op == "..") return 4;
        if (op == "+" || op == "-") return 5;
        if (op == "*" || op == "/" || op == "//" || op == "%") return 6;
        if (op == "^") return 7;
        return -1;
    }

    Expr parse_expression(int minimum_precedence) {
        skip();
        if (cursor_ < tokens_.size() &&
            (tokens_[cursor_].text == "-" || tokens_[cursor_].text == "not" ||
             tokens_[cursor_].text == "#")) {
            const std::string op = tokens_[cursor_++].text;
            Expr unary;
            unary.kind = Expr::Kind::Unary;
            unary.text = op;
            unary.children.push_back(parse_expression(8));
            return unary;
        }
        Expr left = parse_primary();
        while (true) {
            const std::string op = peek();
            const int current_precedence = precedence(op);
            if (current_precedence < minimum_precedence) {
                break;
            }
            ++cursor_;
            Expr binary;
            binary.kind = Expr::Kind::Binary;
            binary.text = op;
            binary.children.push_back(std::move(left));
            binary.children.push_back(parse_expression(
                current_precedence + (op == "^" || op == ".." ? 0 : 1)));
            left = std::move(binary);
        }
        return left;
    }

    Chunk parse_block(const std::unordered_set<std::string>& stops) {
        Chunk chunk;
        while (cursor_ < tokens_.size()) {
            const std::string next = peek();
            if (next.empty() || terminator(next, stops)) {
                break;
            }
            const std::size_t before = cursor_;
            chunk.body.push_back(parse_statement());
            if (cursor_ == before) {
                ++cursor_;
            }
        }
        return chunk;
    }

    Stmt parse_statement() {
        const std::string kind = peek();
        if (kind == "local") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::Local;
            if (take("function")) {
                statement.kind = Stmt::Kind::Function;
                skip();
                if (cursor_ < tokens_.size()) {
                    statement.name = tokens_[cursor_++].text;
                }
                parse_function_tail(statement);
                return statement;
            }
            while (true) {
                skip();
                if (cursor_ >= tokens_.size() || tokens_[cursor_].kind != Token::Kind::Word) {
                    break;
                }
                statement.names.push_back(tokens_[cursor_++].text);
                if (!take(",")) {
                    break;
                }
            }
            if (take("=")) {
                while (cursor_ < tokens_.size()) {
                    statement.values.push_back(parse_expression(0));
                    if (!take(",")) {
                        break;
                    }
                }
            }
            return statement;
        }
        if (kind == "return") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::Return;
            while (cursor_ < tokens_.size()) {
                const std::string next = peek();
                if (next.empty() || next == "end" || next == "else" ||
                    next == "elseif" || next == "until") {
                    break;
                }
                statement.values.push_back(parse_expression(0));
                if (!take(",")) {
                    break;
                }
            }
            return statement;
        }
        if (kind == "break" || kind == "continue") {
            ++cursor_;
            Stmt statement;
            statement.kind = kind == "break" ? Stmt::Kind::Break : Stmt::Kind::Continue;
            return statement;
        }
        if (kind == "if") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::If;
            statement.values.push_back(parse_expression(0));
            take("then");
            statement.body = parse_block({"elseif", "else", "end"}).body;
            while (take("elseif")) {
                Stmt branch;
                branch.kind = Stmt::Kind::If;
                branch.values.push_back(parse_expression(0));
                take("then");
                branch.body = parse_block({"elseif", "else", "end"}).body;
                statement.otherwise.push_back(std::move(branch));
            }
            if (take("else")) {
                statement.otherwise = parse_block({"end"}).body;
            }
            take("end");
            return statement;
        }
        if (kind == "while") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::While;
            statement.values.push_back(parse_expression(0));
            take("do");
            statement.body = parse_block({"end"}).body;
            take("end");
            return statement;
        }
        if (kind == "repeat") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::Repeat;
            statement.body = parse_block({"until"}).body;
            take("until");
            statement.values.push_back(parse_expression(0));
            return statement;
        }
        if (kind == "for") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::For;
            while (cursor_ < tokens_.size() && peek() != "do") {
                statement.values.push_back(parse_expression(0));
                if (!take(",")) {
                    if (peek() != "in" && peek() != "=") {
                        ++cursor_;
                    }
                }
            }
            take("do");
            statement.body = parse_block({"end"}).body;
            take("end");
            return statement;
        }
        if (kind == "function") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::Function;
            skip();
            if (cursor_ < tokens_.size()) {
                statement.name = tokens_[cursor_++].text;
            }
            parse_function_tail(statement);
            return statement;
        }
        if (kind == "do") {
            ++cursor_;
            Stmt statement;
            statement.kind = Stmt::Kind::Block;
            statement.body = parse_block({"end"}).body;
            take("end");
            return statement;
        }
        if (kind == "type" || kind == "export") {
            Stmt statement;
            statement.kind = Stmt::Kind::Type;
            while (cursor_ < tokens_.size() && peek() != "end") {
                const std::string value = peek();
                if (value == "local" || value == "return" || value == "function" ||
                    value == "if" || value == "while") {
                    break;
                }
                statement.name += value;
                ++cursor_;
                if (statement.name.size() > 4096) {
                    break;
                }
            }
            return statement;
        }

        Stmt statement;
        statement.kind = Stmt::Kind::Opaque;
        statement.values.push_back(parse_expression(0));
        if (take("=")) {
            statement.kind = Stmt::Kind::Assign;
            while (cursor_ < tokens_.size()) {
                statement.values.push_back(parse_expression(0));
                if (!take(",")) {
                    break;
                }
            }
        } else if (!statement.values.empty() &&
                   statement.values.front().kind == Expr::Kind::Call) {
            statement.kind = Stmt::Kind::Call;
        }
        return statement;
    }

    void parse_function_tail(Stmt& statement) {
        if (take("(")) {
            while (cursor_ < tokens_.size() && peek() != ")") {
                skip();
                if (cursor_ < tokens_.size()) {
                    statement.names.push_back(tokens_[cursor_++].text);
                }
                if (!take(",")) {
                    break;
                }
            }
            take(")");
        }
        statement.body = parse_block({"end"}).body;
        take("end");
    }
};

enum class OpCode : std::uint8_t {
    Move, LoadNil, LoadBool, LoadConst, LoadGlobal, StoreGlobal, GetUpvalue,
    SetUpvalue, GetTable, SetTable, GetField, SetField, NewTable, SetList,
    Add, Sub, Mul, Div, Mod, Pow, Neg, Not, Len, Concat, Equal, Less,
    LessEqual, Test, TestSet, Jump, JumpIfFalse, JumpIfTrue, Call, TailCall,
    Return, Closure, Close, Vararg, ForPrep, ForLoop, TForCall, TForLoop,
    SetTop, Pop, Dup, Self, Push, PopN, CheckStack, GetIndex, SetIndex,
    MakeTuple, Unpack, Yield, Resume, PCall, XPCall, Assert, TypeOf, Nop,
    Dead0, Dead1, Dead2, Dead3, Dead4, Dead5, Dead6, Dead7, Dead8, Dead9,
    Dead10, Dead11, Dead12, Dead13, Dead14, Dead15, Dead16, Dead17
};

struct Instruction {
    OpCode op = OpCode::Nop;
    int a = 0;
    int b = 0;
    int c = 0;
};

struct StackChunk {
    std::vector<std::string> constants;
    std::vector<Instruction> code;
    std::vector<StackChunk> prototypes;
};

struct RegisterInstruction {
    OpCode op = OpCode::Nop;
    int a = 0;
    int b = 0;
    int c = 0;
};

struct RegisterChunk {
    std::vector<std::string> constants;
    std::vector<RegisterInstruction> code;
    std::vector<RegisterChunk> prototypes;
    unsigned max_registers = 0;
};

static int add_constant(StackChunk& chunk, const std::string& value) {
    const auto found = std::find(chunk.constants.begin(), chunk.constants.end(), value);
    if (found != chunk.constants.end()) {
        return static_cast<int>(found - chunk.constants.begin());
    }
    chunk.constants.push_back(value);
    return static_cast<int>(chunk.constants.size() - 1);
}

static void compile_expression(StackChunk& chunk, const Expr& expression) {
    for (const Expr& child : expression.children) {
        compile_expression(chunk, child);
    }
    switch (expression.kind) {
    case Expr::Kind::Name:
        chunk.code.push_back({OpCode::LoadGlobal, add_constant(chunk, expression.text), 0, 0});
        break;
    case Expr::Kind::Literal:
        chunk.code.push_back({OpCode::LoadConst, add_constant(chunk, expression.text), 0, 0});
        break;
    case Expr::Kind::Unary:
        chunk.code.push_back({expression.text == "not" ? OpCode::Not : OpCode::Neg, 0, 0, 0});
        break;
    case Expr::Kind::Binary:
        chunk.code.push_back({OpCode::Add, 0, 0, 0});
        break;
    case Expr::Kind::Call:
        chunk.code.push_back({OpCode::Call, static_cast<int>(expression.children.size()), 0, 0});
        break;
    case Expr::Kind::Index:
    case Expr::Kind::Member:
        chunk.code.push_back({OpCode::GetTable, 0, 0, 0});
        break;
    case Expr::Kind::Table:
        chunk.code.push_back({OpCode::NewTable, 0, 0, 0});
        break;
    case Expr::Kind::Function:
        chunk.code.push_back({OpCode::Closure, 0, 0, 0});
        break;
    default:
        chunk.code.push_back({OpCode::Nop, 0, 0, 0});
        break;
    }
}

static void compile_statements(StackChunk& chunk, const std::vector<Stmt>& statements) {
    for (const Stmt& statement : statements) {
        for (const Expr& value : statement.values) {
            compile_expression(chunk, value);
        }
        switch (statement.kind) {
        case Stmt::Kind::Local:
            for (std::size_t i = 0; i < statement.names.size(); ++i) {
                chunk.code.push_back({OpCode::SetTop, static_cast<int>(i), 0, 0});
            }
            break;
        case Stmt::Kind::Assign:
            chunk.code.push_back({OpCode::StoreGlobal, 0, 0, 0});
            break;
        case Stmt::Kind::Return:
            chunk.code.push_back({OpCode::Return, static_cast<int>(statement.values.size()), 0, 0});
            break;
        case Stmt::Kind::If:
            compile_statements(chunk, statement.body);
            compile_statements(chunk, statement.otherwise);
            chunk.code.push_back({OpCode::JumpIfFalse, 0, 0, 0});
            break;
        case Stmt::Kind::While:
        case Stmt::Kind::Repeat:
        case Stmt::Kind::For:
            compile_statements(chunk, statement.body);
            chunk.code.push_back({OpCode::Jump, 0, 0, 0});
            break;
        case Stmt::Kind::Function:
            compile_statements(chunk, statement.body);
            chunk.code.push_back({OpCode::Closure, 0, 0, 0});
            break;
        case Stmt::Kind::Break:
            chunk.code.push_back({OpCode::Jump, 0, 0, 0});
            break;
        default:
            chunk.code.push_back({OpCode::Pop, 1, 0, 0});
            break;
        }
    }
    chunk.code.push_back({OpCode::Return, 0, 0, 0});
}

static StackChunk compile_chunk(const Chunk& chunk) {
    StackChunk compiled;
    compile_statements(compiled, chunk.body);
    return compiled;
}

static RegisterChunk register_compile(const StackChunk& stack) {
    RegisterChunk registers;
    registers.constants = stack.constants;
    registers.max_registers = 8;
    for (const Instruction& instruction : stack.code) {
        registers.code.push_back(
            {instruction.op, instruction.a, instruction.b, instruction.c});
    }
    for (const StackChunk& prototype : stack.prototypes) {
        RegisterChunk child = register_compile(prototype);
        registers.max_registers = std::max(registers.max_registers, child.max_registers);
        registers.prototypes.push_back(std::move(child));
    }
    return registers;
}

static std::string decode_string(const std::string& quoted) {
    if (quoted.size() < 2 ||
        (quoted.front() != '"' && quoted.front() != '\'' && quoted.front() != '`') ||
        quoted.back() != quoted.front()) {
        return {};
    }
    std::string value;
    for (std::size_t i = 1; i + 1 < quoted.size(); ++i) {
        unsigned char c = static_cast<unsigned char>(quoted[i]);
        if (c != '\\') {
            value.push_back(static_cast<char>(c));
            continue;
        }
        if (++i + 1 >= quoted.size()) {
            break;
        }
        const char escaped = quoted[i];
        switch (escaped) {
        case 'n': value.push_back('\n'); break;
        case 'r': value.push_back('\r'); break;
        case 't': value.push_back('\t'); break;
        case 'b': value.push_back('\b'); break;
        case 'f': value.push_back('\f'); break;
        case 'v': value.push_back('\v'); break;
        case '\\': value.push_back('\\'); break;
        case '"': value.push_back('"'); break;
        case '\'': value.push_back('\''); break;
        default:
            if (escaped >= '0' && escaped <= '9') {
                int number = escaped - '0';
                for (int digit = 0; digit < 2 && i + 1 < quoted.size() - 1 &&
                                    std::isdigit(static_cast<unsigned char>(quoted[i + 1])) != 0;
                     ++digit) {
                    number = number * 10 + (quoted[++i] - '0');
                }
                value.push_back(static_cast<char>(number & 0xff));
            } else if (escaped == 'x' && i + 2 < quoted.size() - 1) {
                const auto hex = [](char digit) -> int {
                    if (digit >= '0' && digit <= '9') return digit - '0';
                    if (digit >= 'a' && digit <= 'f') return digit - 'a' + 10;
                    if (digit >= 'A' && digit <= 'F') return digit - 'A' + 10;
                    return 0;
                };
                const int high = hex(quoted[++i]);
                const int low = hex(quoted[++i]);
                value.push_back(static_cast<char>((high << 4) | low));
            } else {
                value.push_back(escaped);
            }
        }
    }
    return value;
}

static std::string xor_decoder_expression(const std::string& value, unsigned key) {
    std::ostringstream output;
    output << "(function()local __f=function(a,b)local r,p=0,1;while a>0 or b>0 do "
              "local x,y=a%2,b%2;if x~=y then r=r+p end;a=(a-x)/2;b=(b-y)/2;p=p*2 end;"
              "return r end;local __t={";
    for (std::size_t i = 0; i < value.size(); ++i) {
        if (i != 0) output << ',';
        output << (static_cast<unsigned char>(value[i]) ^ key);
    }
    output << "};for i=1,#__t do __t[i]=__f(__t[i]," << key
           << ")end;return string.char(table.unpack(__t))end)()";
    return output.str();
}

static std::string encode_strings(std::vector<Token> tokens, unsigned key) {
    for (Token& token : tokens) {
        if (token.kind != Token::Kind::String || token.text.empty() ||
            token.text.front() == '[' || token.text.front() == '`') {
            continue;
        }
        const std::string decoded = decode_string(token.text);
        if (!decoded.empty()) {
            token.text = xor_decoder_expression(decoded, key);
        }
    }
    return join_tokens(tokens);
}

static std::string rename_locals(std::vector<Token> tokens) {
    std::unordered_map<std::string, std::string> names;
    std::size_t generated = 0;
    auto next_name = [&]() {
        const std::size_t value = generated++;
        return "_l" + std::to_string(value);
    };

    for (std::size_t i = 0; i < tokens.size(); ++i) {
        if (tokens[i].kind != Token::Kind::Word || tokens[i].text != "local") {
            continue;
        }
        std::size_t cursor = i + 1;
        while (cursor < tokens.size() && trivia(tokens[cursor])) ++cursor;
        if (cursor < tokens.size() && tokens[cursor].text == "function") ++cursor;
        while (cursor < tokens.size()) {
            while (cursor < tokens.size() && trivia(tokens[cursor])) ++cursor;
            if (cursor >= tokens.size() || tokens[cursor].kind != Token::Kind::Word ||
                keyword(tokens[cursor].text)) break;
            if (names.find(tokens[cursor].text) == names.end()) {
                names.emplace(tokens[cursor].text, next_name());
            }
            ++cursor;
            while (cursor < tokens.size() && trivia(tokens[cursor])) ++cursor;
            if (cursor >= tokens.size() || tokens[cursor].text != ",") break;
            ++cursor;
        }
    }

    for (std::size_t i = 0; i < tokens.size(); ++i) {
        Token& token = tokens[i];
        if (token.kind != Token::Kind::Word || keyword(token.text)) continue;
        std::size_t previous = i;
        while (previous > 0 && trivia(tokens[previous - 1])) --previous;
        if (previous > 0 && (tokens[previous - 1].text == "." ||
                             tokens[previous - 1].text == ":")) continue;
        const auto found = names.find(token.text);
        if (found != names.end()) token.text = found->second;
    }
    return join_tokens(tokens);
}

static std::string scramble_control_flow(std::vector<Token> tokens, std::uint64_t seed) {
    const unsigned salt = static_cast<unsigned>((seed % 997U) + 3U);
    std::vector<std::pair<std::size_t, std::size_t>> edits;
    for (std::size_t i = 0; i < tokens.size(); ++i) {
        if (tokens[i].kind != Token::Kind::Word ||
            (tokens[i].text != "if" && tokens[i].text != "while")) continue;
        std::size_t depth = 0;
        std::size_t end = i + 1;
        const std::string terminator = tokens[i].text == "if" ? "then" : "do";
        for (; end < tokens.size(); ++end) {
            if (trivia(tokens[end])) continue;
            if (tokens[end].text == "(" || tokens[end].text == "[" ||
                tokens[end].text == "{") ++depth;
            else if (tokens[end].text == ")" || tokens[end].text == "]" ||
                     tokens[end].text == "}") {
                if (depth > 0) --depth;
            } else if (depth == 0 && tokens[end].text == terminator) {
                break;
            }
        }
        if (end > i + 1 && end < tokens.size()) edits.emplace_back(i + 1, end);
    }
    for (auto it = edits.rbegin(); it != edits.rend(); ++it) {
        const std::size_t begin = it->first;
        const std::size_t end = it->second;
        tokens.insert(tokens.begin() + static_cast<std::ptrdiff_t>(end),
                      {Token{Token::Kind::Punct, ") and (" + std::to_string(salt) +
                                  "==" + std::to_string(salt) + "))", 0, {}}});
        tokens.insert(tokens.begin() + static_cast<std::ptrdiff_t>(begin),
                      {Token{Token::Kind::Punct, "((", 0, {}}});
    }
    return join_tokens(tokens);
}

static std::vector<unsigned char> rle_compress(const std::string& source) {
    std::vector<unsigned char> encoded;
    for (std::size_t i = 0; i < source.size();) {
        const unsigned char value = static_cast<unsigned char>(source[i]);
        std::size_t count = 1;
        while (i + count < source.size() &&
               static_cast<unsigned char>(source[i + count]) == value && count < 255) {
            ++count;
        }
        if (count >= 4 || value == 255) {
            encoded.push_back(255);
            encoded.push_back(static_cast<unsigned char>(count));
            encoded.push_back(value);
        } else {
            for (std::size_t j = 0; j < count; ++j) encoded.push_back(value);
        }
        i += count;
    }
    return encoded;
}

static std::string lua_array(const std::vector<unsigned char>& data) {
    std::ostringstream output;
    output << '{';
    for (std::size_t i = 0; i < data.size(); ++i) {
        if (i != 0) output << ',';
        output << static_cast<unsigned>(data[i]);
    }
    output << '}';
    return output.str();
}

static std::vector<unsigned> randomized_opcodes(std::size_t count, std::mt19937_64& rng) {
    std::vector<unsigned> values(count);
    for (std::size_t i = 0; i < count; ++i) values[i] = static_cast<unsigned>(i + 1);
    std::shuffle(values.begin(), values.end(), rng);
    return values;
}

static std::string generate_bootstrap(const std::string& source,
                                      const StackChunk& stack,
                                      const RegisterChunk& registers,
                                      std::mt19937_64& rng) {
    const unsigned guard_seed = static_cast<unsigned>(rng() % 97U) + 3U;
    const std::vector<unsigned> mapping = randomized_opcodes(32, rng);
    std::vector<unsigned char> compressed = rle_compress(source);
    const unsigned payload_key = static_cast<unsigned>(rng() % 251U) + 1U;
    std::vector<unsigned char> encrypted = compressed;
    for (std::size_t i = 0; i < encrypted.size(); ++i) {
        const unsigned mask = (payload_key +
                               static_cast<unsigned>((i * 31U) % 251U)) & 0xffU;
        encrypted[i] = static_cast<unsigned char>(
            static_cast<unsigned>(encrypted[i]) ^ mask);
    }

    constexpr unsigned checksum_modulus = 1000003U;
    unsigned payload_checksum = 0;
    unsigned payload_rolling = 17;
    for (std::size_t i = 0; i < encrypted.size(); ++i) {
        payload_checksum =
            (payload_checksum + static_cast<unsigned>(encrypted[i])) %
            checksum_modulus;
        payload_rolling =
            (payload_rolling * 257U + static_cast<unsigned>(encrypted[i]) +
             static_cast<unsigned>(i)) %
            checksum_modulus;
    }

    unsigned opcode_attestation = guard_seed % checksum_modulus;
    for (std::size_t i = 0; i < 5; ++i) {
        opcode_attestation =
            (opcode_attestation * 33U + mapping[i] +
             static_cast<unsigned>(i + 1)) %
            checksum_modulus;
    }

    (void)stack;
    (void)registers;

    std::ostringstream code;
    code << "--[Luatrix | LTRIX]\n";
    code << "local __lx_args={...};";
    code << "local __lx_blob=" << lua_array(encrypted) << ";";
    code << "local __lx_ids={";
    for (std::size_t i = 0; i < mapping.size(); ++i) {
        if (i != 0) code << ',';
        code << mapping[i];
    }
    code << "};";
    code << "local __lx_code={" << mapping[0] << ',' << mapping[1] << ','
         << mapping[2] << ',' << mapping[3] << ',' << mapping[4] << "};";
    code << "local __lx_vm={pc=1,blob=__lx_blob,key=" << payload_key
         << ",seed=" << guard_seed << ",checksum=" << payload_checksum
         << ",rolling=" << payload_rolling << ",attestation="
         << opcode_attestation << "};";
    code << "local __lx_xor=function(a,b)local r,p=0,1;while a>0 or b>0 do "
            "local x,y=a%2,b%2;if x~=y then r=r+p end;"
            "a=(a-x)/2;b=(b-y)/2;p=p*2 end;return r end;";
    code << "local __lx_byte=function(pos)local mask=("
         << "__lx_vm.key+((pos-1)*31)%251)%256;return __lx_xor("
         << "__lx_vm.blob[pos],mask)end;";
    code << "local __lx_handlers={};";
    for (unsigned id : mapping) {
        code << "__lx_handlers[" << id
             << "]=function(vm)vm.noise=(vm.noise or 0)+1 end;";
    }

    code << "__lx_handlers[" << mapping[0]
         << "]=function(vm)local sum,roll=0,17;"
            "for i=1,#vm.blob do local b=vm.blob[i];"
            "sum=(sum+b)%1000003;roll=(roll*257+b+i-1)%1000003 end;"
            "local att=vm.seed%1000003;"
            "for i=1,#__lx_code do att=(att*33+__lx_code[i]+i)%1000003 end;"
            "if sum~=vm.checksum or roll~=vm.rolling or "
            "att~=vm.attestation or type(loadstring or load)~=\"function\" "
            "or type(string.char)~=\"function\" or type(table.concat)~=\"function\" "
            "then error(\"Luatrix VM integrity failure\") end;"
            "vm.verified=true end;";

    code << "__lx_handlers[" << mapping[1]
         << "]=function(vm)local src={};local pos=1;"
            "while pos<=#vm.blob do local b=__lx_byte(pos);"
            "if b==255 then local count=__lx_byte(pos+1);"
            "local value=__lx_byte(pos+2);"
            "for j=1,count do src[#src+1]=value end;pos=pos+3;"
            "else src[#src+1]=b;pos=pos+1 end end;"
            "vm.src=src end;";

    code << "__lx_handlers[" << mapping[2]
         << "]=function(vm)local pieces={};local piece={};"
            "for i=1,#vm.src do piece[#piece+1]=string.char(vm.src[i]);"
            "if #piece==128 then pieces[#pieces+1]=table.concat(piece);"
            "piece={} end end;if #piece>0 then pieces[#pieces+1]=table.concat(piece) end;"
            "local text=table.concat(pieces);local loader=loadstring or load;"
            "local fn,err=loader(text,\"LTRIX\");text=nil;pieces=nil;piece=nil;"
            "for i=1,#vm.src do vm.src[i]=0 end;vm.src=nil;"
            "if type(fn)~=\"function\" then error(\"Luatrix payload rejected: \"..tostring(err)) end;"
            "vm.fn=fn end;";

    code << "__lx_handlers[" << mapping[3]
         << "]=function(vm)if vm.blob then for i=1,#vm.blob do vm.blob[i]=0 end end;"
            "vm.blob=nil;vm.key=0;vm.checksum=0;vm.rolling=0;vm.wiped=true end;";

    code << "__lx_handlers[" << mapping[4]
         << "]=function(vm)if not vm.fn or not vm.wiped then "
            "error(\"Luatrix VM lifecycle failure\") end;vm.halted=true end;";

    code << "while not __lx_vm.halted do local op=__lx_code[__lx_vm.pc];"
            "local handler=__lx_handlers[op];if not handler then "
            "error(\"Luatrix VM opcode integrity failure\") end;"
            "handler(__lx_vm);__lx_vm.pc=__lx_vm.pc+1;"
            "if __lx_vm.pc>#__lx_code+1 then error(\"Luatrix VM runaway\") end end;";
    code << "local __lx_fn=__lx_vm.fn;__lx_vm.fn=nil;__lx_vm.args=nil;"
         << "return __lx_fn(table.unpack(__lx_args))\n";
    return code.str();
}

static std::string process(const std::string& input) {
    const std::uint64_t timestamp =
        static_cast<std::uint64_t>(std::chrono::high_resolution_clock::now()
                                        .time_since_epoch().count());
    std::random_device entropy;
    std::mt19937_64 rng(timestamp ^ (static_cast<std::uint64_t>(entropy()) << 32U));

    auto checked = lex_checked(input);
    if (!checked.second.empty()) {
        std::ostringstream message;
        message << "lexer: " << checked.second.front().message << " at "
                << checked.second.front().at.line << ':'
                << checked.second.front().at.column;
        throw std::runtime_error(message.str());
    }

    const unsigned string_key = static_cast<unsigned>(rng() % 251U) + 1U;
    std::string transformed = rename_locals(checked.first);
    transformed = scramble_control_flow(lex(transformed), rng());
    transformed = encode_strings(lex(transformed), string_key);

    auto transformed_checked = lex_checked(transformed);
    Parser parser(transformed_checked.first);
    const Chunk ast = parser.parse();
    const StackChunk stack = compile_chunk(ast);
    const RegisterChunk registers = register_compile(stack);
    return generate_bootstrap(transformed, stack, registers, rng);
}

} // namespace luatrix

int main(int argc, char** argv) {
    try {
        if (argc != 3) {
            throw std::runtime_error("usage: luatrix <input> <out>");
        }
        std::ifstream input(argv[1], std::ios::binary);
        if (!input) {
            throw std::runtime_error("cannot open input");
        }
        std::ostringstream contents;
        contents << input.rdbuf();

        std::ofstream output(argv[2], std::ios::binary);
        if (!output) {
            throw std::runtime_error("cannot open output");
        }
        output << luatrix::process(contents.str());
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "luatrix: " << error.what() << '\n';
        return 1;
    }
}