module.exports = grammar({
  name: 'high_level_for_program',

  rules: {
    program: $ => repeat($.func),

    func: $ => seq(
      'def', $.identifier, '(', optional($.arg_list), ')', ':', $.type, ':=', repeat($.stmt)
    ),

    stmt: $ => choice(
      seq('for', '(', $.identifier, ',', $.identifier, ')', 'in', 'enumerate', '(', $.expr, ')', 'do', repeat($.stmt), 'done'),
      seq('for', '(', $.identifier, ',', $.identifier, ')', 'in', 'reversed', '(', 'enumerate', '(', $.expr, ')', ')', 'do', repeat($.stmt), 'done'),
      seq('if', $.expr, 'then', repeat($.stmt), 'endif'),
      seq('if', $.expr, 'then', repeat($.stmt), 'else', repeat($.stmt), 'endif'),
      seq('yield', $.expr),
      seq('return', $.expr),
      seq('let', $.identifier, ':=', $.expr, 'in', repeat($.stmt)),
      seq('let', 'mut', $.identifier, ':=', 'False', 'in', repeat($.stmt)),
      seq($.identifier, ':=', 'True')
    ),

    expr: $ => choice(
      $.expr3,
      seq($.expr3, $.bin_op, $.expr3),
      seq($.expr2, 'and', $.expr1),
      seq($.expr1, 'or', $.expr)
    ),

    expr3: $ => choice(
      $.char,
      $.string,
      seq('[', optional($.expr_list), ']'),
      seq('{', repeat($.stmt), '}'),
      $.identifier,
      seq($.identifier, '(', optional($.ve_arg_list), ')'),
      'True',
      'False',
      seq('not', $.expr3)
    ),

    expr2: $ => $.expr3,
    expr1: $ => $.expr2,

    arg_list: $ => seq($.arg, repeat(seq(',', $.arg))),
    ve_arg_list: $ => seq($.ve_arg, repeat(seq(',', $.ve_arg))),
    expr_list: $ => seq($.expr, repeat(seq(',', $.expr))),

    arg: $ => choice(
      seq($.identifier, ':', $.type),
      seq($.identifier, ':', $.type, 'with', '(', optional($.identifier_list), ')')
    ),

    ve_arg: $ => choice(
      $.expr,
      seq($.expr, 'with', '(', optional($.identifier_list), ')')
    ),

    identifier_list: $ => seq($.identifier, repeat(seq(',', $.identifier))),

    identifier: $ => /[a-zA-Z_][a-zA-Z0-9_]*/,
    char: $ => /'[^']'/,
    string: $ => /"[^"]*"/,

    type: $ => choice($.type1, $.type2),
    type1: $ => choice('Char', seq('[', $.type, ']')),
    type2: $ => 'Bool',

    bin_op: $ => choice('=', '!=', '<=', '<', '>=', '>', '===', '!==', seq('=', $.type, '=')),
  }
});
