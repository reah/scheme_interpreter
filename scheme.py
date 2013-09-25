"""This module implements the core Scheme interpreter functions, including the
eval/apply mutual recurrence, environment model, and read-eval-print loop.
"""

from scheme_primitives import *
from scheme_reader import *
from ucb import main, trace
import string

##############
# Eval/Apply #
##############

def scheme_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV.

    >>> expr = read_line("(+ 2 2)")
    >>> expr
    Pair('+', Pair(2, Pair(2, nil)))
    >>> scheme_eval(expr, create_global_frame())
    4
    """
    if expr is None:
        raise SchemeError("Cannot evaluate an undefined expression.")

    # Evaluate Atoms
    if scheme_symbolp(expr):
        return env.lookup(expr)
    elif scheme_atomp(expr):
        return expr

    # All non-atomic expressions are lists.
    if not scheme_listp(expr):
        raise SchemeError("malformed list: {0}".format(str(expr)))
    first, rest = expr.first, expr.second

    # Evaluate Combinations
    if first in LOGIC_FORMS:
        return scheme_eval(LOGIC_FORMS[first](rest, env), env)
    elif first == "lambda":
        return do_lambda_form(rest, env)
    elif first == "mu":
        return do_mu_form(rest)
    elif first == "define":
        return do_define_form(rest, env)
    elif first == "quote":
        return do_quote_form(rest)
    elif first == "let":
        expr, env = do_let_form(rest, env)
        return scheme_eval(expr, env)
    else:
        procedure = scheme_eval(first, env)
        args = rest.map(lambda operand: scheme_eval(operand, env))
        return scheme_apply(procedure, args, env)

def scheme_apply(procedure, args, env):
    """Apply Scheme PROCEDURE to argument values ARGS in environment ENV."""
    if isinstance(procedure, PrimitiveProcedure):
        return apply_primitive(procedure, args, env)
    elif isinstance(procedure, LambdaProcedure):
        "*** YOUR CODE HERE ***"
        new_frame = procedure.env
        new_frame = new_frame.make_call_frame(procedure.formals, args)
        return scheme_eval(procedure.body, new_frame)
    elif isinstance(procedure, MuProcedure):
        "*** YOUR CODE HERE ***"
        new_frame = env.make_call_frame(procedure.formals, args)
        return scheme_eval(procedure.body, new_frame)
    else:
        # print(repr(procedure))
        raise SchemeError("Cannot call {0}".format(str(procedure)))

def apply_primitive(procedure, args, env):
    """Apply PrimitiveProcedure PROCEDURE to a Scheme list of ARGS in ENV.

    >>> env = create_global_frame()
    >>> plus = env.bindings["+"]
    >>> twos = Pair(2, Pair(2, nil))
    >>> apply_primitive(plus, twos, env)
    4
    """
    "*** YOUR CODE HERE ***"
    args_list = []
    args.map(lambda num: args_list.append(num))
    if procedure.use_env == True:
        args_list.append(env)
    try:
        return procedure.fn(*args_list)
    except TypeError:
        raise SchemeError()

################
# Environments #
################

class Frame(object):
    """An environment frame binds Scheme symbols to Scheme values."""

    def __init__(self, parent):
        """An empty frame with a PARENT frame (that may be None)."""
        self.bindings = {}
        self.parent = parent

    def __repr__(self):
        if self.parent is None:
            return "<Global Frame>"
        else:
            s = sorted('{0}: {1}'.format(k,v) for k,v in self.bindings.items())
            return "<{{{0}}} -> {1}>".format(', '.join(s), repr(self.parent))

    def lookup(self, symbol):
        """Return the value bound to SYMBOL.  Errors if SYMBOL is not found."""
        "*** YOUR CODE HERE ***"
        if symbol in self.bindings.keys():
            return self.bindings[symbol]
        else:
            if self.parent is not None:
                return self.parent.lookup(symbol)
            else:
                raise SchemeError("unknown identifier: {0}".format(str(symbol)))

    def global_frame(self):
        """The global environment at the root of the parent chain."""
        e = self
        while e.parent is not None:
            e = e.parent
        return e

    def make_call_frame(self, formals, vals):
        """Return a new local frame whose parent is SELF, in which the symbols
        in the Scheme formal parameter list FORMALS are bound to the Scheme
        values in the Scheme value list VALS.

        >>> env = create_global_frame()
        >>> formals, vals = read_line("(a b c)"), read_line("(1 2 3)")
        >>> env.make_call_frame(formals, vals)
        <{a: 1, b: 2, c: 3} -> <Global Frame>>
        """
        frame = Frame(self)
        "*** YOUR CODE HERE ***"
        if len(vals) != len(formals):
            raise SchemeError("wrong number of formal values")
        check_formals(formals)
        while formals is not nil and vals is not nil:
            frame.define(formals.first, vals.first)
            formals = formals.second
            vals = vals.second
        """
        for formal in formals:
            # print(repr(formal))
            if formal is not nil and vals is not nil:
                frame.define(formal.first[0], formal.second[0])
                vals = vals.second
        # print(repr(frame))
        """
        """
        for formal in formals:
            frame.define(formals.first, vals.first)
            vals = vals.second
        """
        return frame

    def define(self, sym, val):
        """Define Scheme symbol SYM to have value VAL in SELF."""
        self.bindings[sym] = val

class LambdaProcedure(object):
    """A procedure defined by a lambda expression or the complex define form."""

    def __init__(self, formals, body, env):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY, and whose parent
        environment is the Frame ENV.  A lambda expression containing multiple
        expressions, such as (lambda (x) (display x) (+ x 1)) can be handled by
        using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body
        self.env = env

    def __str__(self):
        return "(lambda {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body, self.env, self.env.bindings)
        return "LambdaProcedure({0}, {1}, {2})".format(*(repr(a) for a in args))

class MuProcedure(object):
    """A procedure defined by a mu expression, which has dynamic scope.
     _________________
    < Scheme is cool! >
     -----------------
            \   ^__^
             \  (oo)\_______
                (__)\       )\/\
                    ||----w |
                    ||     ||
    """

    def __init__(self, formals, body):
        """A procedure whose formal parameter list is FORMALS (a Scheme list),
        whose body is the single Scheme expression BODY.  A mu expression
        containing multiple expressions, such as (mu (x) (display x) (+ x 1))
        can be handled by using (begin (display x) (+ x 1)) as the body."""
        self.formals = formals
        self.body = body

    def __str__(self):
        return "(mu {0} {1})".format(str(self.formals), str(self.body))

    def __repr__(self):
        args = (self.formals, self.body)
        return "MuProcedure({0}, {1})".format(*(repr(a) for a in args))

#################
# Special forms #
#################

def do_lambda_form(vals, env):
    """Evaluate a lambda form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    "*** YOUR CODE HERE ***"
    if len(vals) > 2:
        # Lambda expressions containing multiple expressions
        # eg (lambda (x) (display x) (+ x 1)) -> (lambda (x) (begin (display x) (+ x 1)))
        new_vals = Pair("begin", vals.second)
        return LambdaProcedure(formals, new_vals, env)
    else:
        return LambdaProcedure(formals, vals.second.first, env)

def do_mu_form(vals):
    """Evaluate a mu form with parameters VALS."""
    check_form(vals, 2)
    formals = vals[0]
    check_formals(formals)
    "*** YOUR CODE HERE ***"
    if len(vals) > 2:
        new_vals = Pair("begin", vals.second)
        return MuProcedure(formals, new_vals)
    else:
        return MuProcedure(formals, vals.second.first)

def do_define_form(vals, env):
    """Evaluate a define form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    target = vals[0]
    if scheme_symbolp(target):
        check_form(vals, 2, 2)
        "*** YOUR CODE HERE ***"
        env.bindings[target] = scheme_eval(vals[1], env)

    elif isinstance(target, Pair):
        "*** YOUR CODE HERE ***"
        check_formals(target)
        env.bindings[target.first] = do_lambda_form(Pair(target.second, vals.second), env)
        """
        print("")
        print("Lambda formals: " + repr(lambda_formals))
        print("")
        print("Lambda vals: " + repr(lambda_vals))
        print("")
        print("Lambda eval: " + repr(lambda_eval))

        print("")
        print("Target.first " + repr(target.first))

        print("")
        print("Environment: " + repr(env))
        """
    else:
        raise SchemeError("bad argument to define")

def do_quote_form(vals):
    """Evaluate a quote form with parameters VALS."""
    check_form(vals, 1, 1)
    "*** YOUR CODE HERE ***"
    return vals.first

def do_let_form(vals, env):
    """Evaluate a let form with parameters VALS in environment ENV."""
    check_form(vals, 2)
    bindings = vals[0]
    exprs = vals.second
    if not scheme_listp(bindings):
        raise SchemeError("bad bindings list in let form")

    # Add a frame containing bindings
    names, vals = nil, nil
    "*** YOUR CODE HERE ***"
    """
    while len(bindings) > 0:
        new_env.define(bindings.first.first[0], scheme_eval(bindings.first.second[0], new_env))
        bindings = bindings.second
    """

    for binding in bindings:
        names = Pair(binding.first, names)
        vals = Pair(scheme_eval(binding.second[0], env), vals)
        # new_env.define(binding.first[0], scheme_eval(binding.second[0], new_env))
    new_env = env.make_call_frame(names, vals)

    # Evaluate all but the last expression after bindings, and return the last
    last = len(exprs)-1
    for i in range(0, last):
        scheme_eval(exprs[i], new_env)
    return exprs[last], new_env

#########################
# Logical Special Forms #
#########################

def do_if_form(vals, env):
    """Evaluate if form with parameters VALS in environment ENV."""
    check_form(vals, 3, 3)
    "*** YOUR CODE HERE ***"
    if scheme_true(scheme_eval(vals.first, env)):
        return vals[1]
    return vals[2]

def do_and_form(vals, env):
    """Evaluate short-circuited and with parameters VALS in environment ENV."""
    "*** YOUR CODE HERE ***"
    last_val = None
    if len(vals) == 0:
        return True
    while vals is not nil:
        if scheme_false(scheme_eval(vals.first, env)):
            return False
        last_val = vals.first
        vals = vals.second
    return last_val

def do_or_form(vals, env):
    """Evaluate short-circuited or with parameters VALS in environment ENV."""
    "*** YOUR CODE HERE ***"
    last_val = None
    if len(vals) == 0:
        return False
    while vals is not nil:
        if not scheme_false(scheme_eval(vals.first, env)):
            return vals.first
        last_val = vals.first
        vals = vals.second  
    return last_val

def do_cond_form(vals, env):
    """Evaluate cond form with parameters VALS in environment ENV."""
    num_clauses = len(vals)
    for i, clause in enumerate(vals):
        check_form(clause, 1)
        if clause.first == "else":
            if i < num_clauses-1:
                raise SchemeError("else must be last")
            test = True
            if clause.second is nil:
                raise SchemeError("badly formed else clause")
        else:
            test = scheme_eval(clause.first, env)
        if test:
            # The first expression evaluates to True
            "*** YOUR CODE HERE ***"
            if clause.second:
                if len(clause.second) > 1:
                    return Pair("begin", clause.second)
                return clause.second[0]
            return test

def do_begin_form(vals, env):
    """Evaluate begin form with parameters VALS in environment ENV."""
    check_form(vals, 1)
    "*** YOUR CODE HERE ***"
    while len(vals) > 1:
        scheme_eval(vals.first, env)
        vals = vals.second
    return vals.first

LOGIC_FORMS = {
        "and": do_and_form,
        "or": do_or_form,
        "if": do_if_form,
        "cond": do_cond_form,
        "begin": do_begin_form,
        }

# Utility methods for checking the structure of Scheme programs

def check_form(expr, min, max = None):
    """Check EXPR (default SELF.expr) is a proper list whose length is
    at least MIN and no more than MAX (default: no maximum). Raises
    a SchemeError if this is not the case."""
    if not scheme_listp(expr):
        raise SchemeError("badly formed expression: " + str(expr))
    length = len(expr)
    if length < min:
        raise SchemeError("too few operands in form")
    elif max is not None and length > max:
        raise SchemeError("too many operands in form")

def check_formals(formals):
    """Check that FORMALS is a valid parameter list, a Scheme list of symbols
    in which each symbol is distinct.

    >>> check_formals(read_line("(a b c)"))
    """
    "*** YOUR CODE HERE ***"
    symbol_list = []
    while formals is not nil:
        if formals.first not in symbol_list:
            if scheme_symbolp(formals.first):
                symbol_list.append(formals.first)
        else:
            raise SchemeError("Not a well-formed list of symbols or symbols are repeated.")
        formals = formals.second


##################
# Tail Recursion #
##################

def scheme_optimized_eval(expr, env):
    """Evaluate Scheme expression EXPR in environment ENV."""
    while True:
        if expr is None:
            raise SchemeError("Cannot evaluate an undefined expression.")

        # Evaluate Atoms
        if scheme_symbolp(expr):
            return env.lookup(expr)
        elif scheme_atomp(expr):
            return expr

        # All non-atomic expressions are lists.
        if not scheme_listp(expr):
            raise SchemeError("malformed list: {0}".format(str(expr)))
        first, rest = expr.first, expr.second

        # Evaluate Combinations
        if first in LOGIC_FORMS:
            "*** YOUR CODE HERE ***"
            expr = LOGIC_FORMS[first](rest, env)
        elif first == "lambda":
            return do_lambda_form(rest, env)
        elif first == "mu":
            return do_mu_form(rest)
        elif first == "define":
            return do_define_form(rest, env)
        elif first == "quote":
            return do_quote_form(rest)
        elif first == "let":
            "*** YOUR CODE HERE ***"
            expr, env = do_let_form(rest, env)
        else:
            "*** YOUR CODE HERE ***"
            procedure = scheme_optimized_eval(first, env)
            args = rest.map(lambda operand: scheme_optimized_eval(operand, env))
            if isinstance(procedure, PrimitiveProcedure):
                return apply_primitive(procedure, args, env)
            elif isinstance(procedure, LambdaProcedure):
                "*** YOUR CODE HERE ***"
                new_frame = procedure.env
                new_frame = new_frame.make_call_frame(procedure.formals, args)
                expr, env = procedure.body, new_frame
            elif isinstance(procedure, MuProcedure):
                "*** YOUR CODE HERE ***"
                new_frame = env.make_call_frame(procedure.formals, args)
                expr, env = procedure.body, new_frame
            else:
                # print(repr(procedure))
                raise SchemeError("Cannot call {0}".format(str(procedure)))
################################################################
# Uncomment the following line to apply tail call optimization #
################################################################
scheme_eval = scheme_optimized_eval


################
# Input/Output #
################

def read_eval_print_loop(next_line, env):
    """Read and evaluate input until an end of file or keyboard interrupt."""
    while True:
        try:
            src = next_line()
            while src.more_on_line:
                expression = scheme_read(src)
                result = scheme_eval(expression, env)
                if result is not None:
                    print(result)
        except (SchemeError, SyntaxError, ValueError) as err:
            print("Error:", err)
        except (KeyboardInterrupt, EOFError):  # <Control>-D, etc.
            return

def scheme_load(sym, env):
    """Load Scheme source file named SYM in environment ENV."""
    check_type(sym, scheme_symbolp, 0, "load")
    with scheme_open(sym) as infile:
        lines = infile.readlines()
    def next_line():
        return buffer_lines(lines)
    read_eval_print_loop(next_line, env.global_frame())

def scheme_open(filename):
    """If either FILENAME or FILENAME.scm is the name of a valid file,
    return a Python file opened to it. Otherwise, raise an error."""
    try:
        return open(filename)
    except IOError as exc:
        if filename.endswith('.scm'):
            raise SchemeError(str(exc))
    try:
        return open(filename + '.scm')
    except IOError as exc:
        raise SchemeError(str(exc))

def create_global_frame():
    """Initialize and return a single-frame environment with built-in names."""
    env = Frame(None)
    env.define("eval", PrimitiveProcedure(scheme_eval, True))
    env.define("apply", PrimitiveProcedure(scheme_apply, True))
    env.define("load", PrimitiveProcedure(scheme_load, True))
    add_primitives(env)
    return env

@main
def run(*argv):
    next_line = buffer_input
    if argv:
        try:
            filename = argv[0]
            input_file = open(argv[0])
            lines = input_file.readlines()
            def next_line():
                return buffer_lines(lines)
        except IOError as err:
            # print(err)
            sys.exit(1)
    read_eval_print_loop(next_line, create_global_frame())
