"""
loosely coupled sudoku problems as testing
"""

#pylint:disable=invalid-name

from typing import Dict, Any, Tuple, List
# pylint:disable=import-error
from constraint import AllDifferentConstraint
import constraint
from constraint2.problem_cached import ProblemCached, SolutionType

BOARD_SIZE = 9
NUM_SQUARES = 3
SQUARE_SIZE = 3

def print_board(my_sol:Dict[str,Any],
    my_var_names:Dict[Tuple[int,int],str],
    extras:List[str],my_board_size:int =BOARD_SIZE) -> None:
    """nothing"""
    for i_dx in range(my_board_size):
        for j_dx in range(my_board_size):
            print(my_sol[my_var_names[i_dx,j_dx]],end=" ")
        print("")
    for extra in extras:
        print(f"{extra} -> {my_sol[extra]}")

def make_empty_board(prefix: str = "x") -> Tuple[ProblemCached,Dict[Tuple[int,int],str]]:
    """
    an empty ordinary Sudoku board
    """
    my_p = ProblemCached()
    my_var_names = {}
    for idx in range(BOARD_SIZE):
        for jdx in range(BOARD_SIZE):
            my_var_names[idx,jdx] = f"{prefix}_{idx,jdx}"
            my_p.addVariable(my_var_names[idx,jdx], range(1,BOARD_SIZE+1))
    for idx in range(BOARD_SIZE):
        my_p.addConstraint(AllDifferentConstraint(),
                           [my_var_names[idx,jdx] for jdx in range(BOARD_SIZE)])
        my_p.addConstraint(AllDifferentConstraint(),
                           [my_var_names[jdx,idx] for jdx in range(BOARD_SIZE)])
    for idx in range(NUM_SQUARES):
        for jdx in range(NUM_SQUARES):
            my_p.addConstraint(AllDifferentConstraint(),
                [my_var_names[idx2,jdx2]
                 for idx2 in range(idx*SQUARE_SIZE,idx*SQUARE_SIZE+SQUARE_SIZE)
                 for jdx2 in range(jdx*SQUARE_SIZE,jdx*SQUARE_SIZE+SQUARE_SIZE)])
    return my_p, my_var_names

def satisfies_regular_sudoku_constraints(sol : SolutionType, var_names : Dict[Tuple[int,int],str]):
    """
    the ordinary sudoku constraints
    """
    for idx in range(BOARD_SIZE):
        row_idx = [sol[var_name] for var_name in (var_names[idx,jdx] for jdx in range(BOARD_SIZE))]
        row_idx.sort()
        assert row_idx == list(range(1,10))
        col_idx = [sol[var_name] for var_name in (var_names[jdx,idx] for jdx in range(BOARD_SIZE))]
        col_idx.sort()
        assert col_idx == list(range(1,10))
    for idx in range(NUM_SQUARES):
        for jdx in range(NUM_SQUARES):
            cur_square = [sol[var_names[idx2,jdx2]]
                 for idx2 in range(idx*SQUARE_SIZE,idx*SQUARE_SIZE+SQUARE_SIZE)
                 for jdx2 in range(jdx*SQUARE_SIZE,jdx*SQUARE_SIZE+SQUARE_SIZE)]
            cur_square.sort()
            assert cur_square == list(range(1,10))

def with_first_4_set():
    """
    top left corner filled with 1,2,3,4
    """
    p, var_names = make_empty_board()
    p.addConstraint(lambda x: x==1,[var_names[0,0]])
    p.addConstraint(lambda x: x==2,[var_names[0,1]])
    p.addConstraint(lambda x: x==3,[var_names[0,2]])
    p.addConstraint(lambda x: x==4,[var_names[0,3]])
    p.makeSolutionIter()
    sol = p.getSolution()
    return sol, p, var_names

def test_with_first_4_set():
    """
    solution satisfies the expected constraints
    """
    sol,_, var_names = with_first_4_set()
    assert sol[var_names[0,0]] == 1
    assert sol[var_names[0,1]] == 2
    assert sol[var_names[0,2]] == 3
    assert sol[var_names[0,3]] == 4
    satisfies_regular_sudoku_constraints(sol, var_names)

def test_with_disjoint_junk():
    """
    a disjoint junk variable
    iterating through solutions does not change the board
    avoiding that extra work
    """
    sol, p, var_names = with_first_4_set()
    p.addVariable("junk",range(1,BOARD_SIZE+1))
    for junk_value in range(1,BOARD_SIZE+1):
        sol = p.getSolution()
        if junk_value>1:
            for var_name in var_names.values():
                assert sol[var_name] == sol_board_only[var_name]
        else:
            satisfies_regular_sudoku_constraints(sol, var_names)
            sol_board_only = {var_name:sol[var_name] for var_name in var_names.values()}
        assert sol["junk"] == junk_value
    constrained_junk = 4
    p.addConstraint(lambda x: x==constrained_junk,["junk"])
    sol = p.getSolution()
    satisfies_regular_sudoku_constraints(sol, var_names)
    assert sol["junk"] == constrained_junk

def test_two_options():
    """
    only 0,1 possible
    """
    my_q = ProblemCached()
    my_q.addVariable("junk2",[0,1])
    my_q.addConstraint(lambda x: x==0,["junk2"])
    my_q.makeSolutionIter()
    sol = my_q.getSolution()
    assert sol == {"junk2": 0}

def test_combine():
    """
    disjoint combine
    """
    sol, p, var_names = with_first_4_set()
    p.addVariable("junk",range(1,BOARD_SIZE+1))
    for _ in range(1,BOARD_SIZE+1):
        sol = p.getSolution()
    constrained_junk = 4
    p.addConstraint(lambda x: x==constrained_junk,["junk"])
    sol = p.getSolution()

    my_q = ProblemCached()
    my_q.addVariable("junk2",[0,1])
    my_q.addConstraint(lambda x: x==0,["junk2"])
    my_q.makeSolutionIter()
    sol = my_q.getSolution()

    p.combine_problems(my_q)
    sol = p.getSolution()
    assert sol[var_names[0,0]] == 1
    assert sol[var_names[0,1]] == 2
    assert sol[var_names[0,2]] == 3
    assert sol[var_names[0,3]] == 4
    satisfies_regular_sudoku_constraints(sol, var_names)
    assert sol["junk"] == constrained_junk
    assert sol["junk2"] in {0,1}

def test_two_by_two():
    """
    junk1 and junk2 each have two possibilities
    both small so the solution iterators are combined
    with starmap
    """
    q1 = ProblemCached()
    q1.addVariable("junk1",[0,1])
    q1.addConstraint(lambda x: x==0,["junk1"])
    q1.makeSolutionIter()
    q1_sol = q1.getSolution()
    assert q1_sol == {"junk1":0}
    q2 = ProblemCached()
    q2.addVariable("junk2",[0,1])
    q2.makeSolutionIter()
    q2_sol = q2.getSolution()
    first_junk2 = q2_sol["junk2"]
    assert first_junk2 in (0,1)
    assert q2_sol == {"junk2":first_junk2}
    q1.combine_problems(q2,True)
    both_sols = q1.getSolutions()
    assert both_sols == [{"junk1":0,"junk2":first_junk2},{"junk1":0,"junk2":1-first_junk2}]

def test_weakly_coupled_sudokus():
    """
    two boards that are independent except for top left entry which is constrained to be the same
    """
    board_1, names_1 = make_empty_board()
    board_2, names_2 = make_empty_board("y")
    board_1.loosely_couple(board_2, True, [
        (constraint.AllEqualConstraint(),[names_1[0,0],names_2[0,0]])
        ])
    sol = board_1.getSolution()
    assert sol[names_1[0,0]] == sol[names_2[0,0]]
    satisfies_regular_sudoku_constraints(sol, names_1)
    satisfies_regular_sudoku_constraints(sol, names_2)
