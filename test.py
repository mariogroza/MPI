import copy
import random
import time
import threading
from threading import Timer


def load_formulas_from_file():
    filename = "benchmark_formulas.txt"
    try:
        with open(filename, 'r') as f:
            lines = f.readlines()
            formulas = [eval(line.strip()) for line in lines if line.strip()]
            assert all(isinstance(f, list) and all(isinstance(clause, list) for clause in f) for f in formulas)
            return formulas
    except Exception as e:
        print("Error reading file:", e)
        return []


def dpll(formula, assignment={}):
    formula = simplify(formula, assignment)

    if not formula:
        return assignment  # Formula is satisfied (no clauses left)

    if any([clause == [] for clause in formula]):
        return None  # Empty clause means conflict, unsatisfiable

    var = choose_variable(formula)

    for val in [True, False]:
        new_assignment = assignment.copy()
        new_assignment[var] = val
        result = dpll(copy.deepcopy(formula), new_assignment)
        if result is not None:
            return result  # Found a valid assignment

    return None  # No valid assignment found, unsatisfiable


def dp(formula):
    formula = copy.deepcopy(formula)

    if not formula:
        return True  # Empty formula is satisfiable

    if any(clause == [] for clause in formula):
        return False  # Empty clause means unsatisfiable

    vars = {abs(lit) for clause in formula for lit in clause}

    if not vars:
        return True  # No variables left

    var = next(iter(vars))
    formula_with_var = eliminate_var(formula, var)

    if any(clause == [] for clause in formula_with_var):
        return False

    return dp(formula_with_var)


def resolution(formula):
    clauses = set(frozenset(c) for c in formula)
    new = set()

    while True:
        pairs = [(c1, c2) for c1 in clauses for c2 in clauses if c1 != c2]
        new.clear()

        for (c1, c2) in pairs:
            resolvents = resolve(c1, c2)
            if frozenset() in resolvents:
                return False  # Found empty clause, unsatisfiable
            new.update(resolvents)

        if new.issubset(clauses):
            return True  # No new clauses added, formula is satisfiable

        clauses.update(new)


def cdcl(formula):
    formula = copy.deepcopy(formula)

    if not formula:
        return {}  # Empty formula is satisfiable

    if any(clause == [] for clause in formula):
        return None  # Empty clause means unsatisfiable

    assignment = {}
    decision_level = 0
    decision_stack = []

    while True:
        unit_prop_result = unit_propagation(formula, assignment)
        if unit_prop_result is False:
            if decision_level == 0:
                return None  # UNSAT - conflict at decision level 0

            # Backtrack
            while decision_stack and decision_stack[-1][1] == decision_level:
                var, _ = decision_stack.pop()
                del assignment[var]

            if not decision_stack:
                return None  # UNSAT - no more decisions to backtrack

            last_decision_var, last_level = decision_stack.pop()
            decision_level = last_level
            assignment[last_decision_var] = False  # Flip the decision
            decision_stack.append((last_decision_var, decision_level))
            continue

        # Check if all variables are assigned
        all_vars = set(abs(lit) for clause in formula for lit in clause)
        unassigned_vars = [var for var in all_vars if var not in assignment]

        if not unassigned_vars:
            return assignment  # All variables assigned without conflict - SAT

        # Make a new decision
        decision_level += 1
        var = unassigned_vars[0]  # Choose the first unassigned variable
        assignment[var] = True
        decision_stack.append((var, decision_level))


def unit_propagation(formula, assignment):
    formula = simplify(formula, assignment)

    if not formula:
        return True  # Empty formula is satisfiable

    if any(clause == [] for clause in formula):
        return False  # Empty clause means unsatisfiable

    # Find unit clauses
    unit_clauses = [clause[0] for clause in formula if len(clause) == 1]

    if not unit_clauses:
        return True  # No unit clauses to propagate

    for lit in unit_clauses:
        var = abs(lit)
        val = lit > 0

        if var in assignment and assignment[var] != val:
            return False  # Conflict in assignment

        assignment[var] = val

    # Recursively continue unit propagation
    return unit_propagation(simplify(formula, assignment), assignment)


def simplify(formula, assignment):
    new_formula = []
    for clause in formula:
        new_clause = []
        satisfied = False

        for lit in clause:
            var = abs(lit)
            if var in assignment:
                val = assignment[var]
                if (lit > 0 and val) or (lit < 0 and not val):
                    satisfied = True
                    break
            else:
                new_clause.append(lit)

        if satisfied:
            continue

        if new_clause:
            new_formula.append(new_clause)
        else:
            new_formula.append([])  # Empty clause indicates unsatisfiable

    return new_formula


def choose_variable(formula):
    # Use a simple heuristic: choose the variable that appears most frequently
    var_count = {}

    for clause in formula:
        for lit in clause:
            var = abs(lit)
            var_count[var] = var_count.get(var, 0) + 1

    if not var_count:
        return None

    return max(var_count.items(), key=lambda x: x[1])[0]


def eliminate_var(formula, var):
    pos_clauses = [c for c in formula if var in c]
    neg_clauses = [c for c in formula if -var in c]
    other_clauses = [c for c in formula if var not in c and -var not in c]

    # Generate resolvents
    resolvents = []
    for pos in pos_clauses:
        for neg in neg_clauses:
            resolvent = [lit for lit in pos + neg if lit != var and lit != -var]
            # Remove duplicates
            resolvent = list(set(resolvent))
            # Check if resolvent is a tautology
            if not any(lit in resolvent and -lit in resolvent for lit in resolvent):
                resolvents.append(resolvent)

    return other_clauses + resolvents


def resolve(c1, c2):
    c1_set = set(c1)
    c2_set = set(c2)
    resolvents = set()

    for lit in c1_set:
        if -lit in c2_set:
            resolvent = (c1_set | c2_set) - {lit, -lit}
            # Skip tautological clauses
            if not any(-l in resolvent for l in resolvent):
                resolvents.add(frozenset(resolvent))

    return resolvents


class TimeoutException(Exception):
    pass


# Windows-compatible timeout implementation
def run_with_timeout(func, args=(), kwargs={}, timeout_duration=10):
    """Run a function with a timeout using threading (works on Windows)"""
    result = [None]
    exception = [None]
    completed = [False]

    def target():
        try:
            result[0] = func(*args, **kwargs)
            completed[0] = True
        except Exception as e:
            exception[0] = e

    thread = threading.Thread(target=target)
    thread.daemon = True

    thread.start()
    thread.join(timeout_duration)

    if not completed[0]:
        return "TIMED OUT", None
    if exception[0]:
        return f"ERROR: {str(exception[0])}", None
    return "COMPLETED", result[0]


def solve_with_timeout(algo_name, formula, timeout=60):
    if algo_name == "dpll":
        status, result = run_with_timeout(dpll, args=(copy.deepcopy(formula),), timeout_duration=timeout)
        if status == "COMPLETED":
            return "SATISFIABLE" if result else "UNSATISFIABLE", result
        return status, None
    elif algo_name == "dp":
        status, result = run_with_timeout(dp, args=(formula,), timeout_duration=timeout)
        if status == "COMPLETED":
            return "SATISFIABLE" if result else "UNSATISFIABLE", None
        return status, None
    elif algo_name == "resolution":
        status, result = run_with_timeout(resolution, args=(formula,), timeout_duration=timeout)
        if status == "COMPLETED":
            return "SATISFIABLE" if result else "UNSATISFIABLE", None
        return status, None
    elif algo_name == "cdcl":
        status, result = run_with_timeout(cdcl, args=(formula,), timeout_duration=timeout)
        if status == "COMPLETED":
            return "SATISFIABLE" if result else "UNSATISFIABLE", result
        return status, None
    else:
        return "Unknown algorithm", None


def main():
    print("SAT Solver Console")
    print("Choose algorithm: dpll / dp / resolution / cdcl")
    algo = input("Algorithm: ").strip().lower()

    formulas = load_formulas_from_file()
    if not formulas:
        print("No valid formulas loaded.")
        return

    start_time = time.time()

    for i, formula in enumerate(formulas):
        print(f"\nFormula {i + 1}:")
        print(f"Formula: {formula}")

        formula_start_time = time.time()
        result_status, assignment = solve_with_timeout(algo, formula)
        formula_end_time = time.time()

        print(f"{result_status}")
        if assignment:
            print("Assignment:", assignment)

        print(f"Formula solving time: {formula_end_time - formula_start_time:.4f} seconds")

    end_time = time.time()
    print(f"\nTotal execution time: {end_time - start_time:.4f} seconds")


if __name__ == "__main__":
    main()