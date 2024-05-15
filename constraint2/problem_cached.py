"""
Avoid solution recomputation when already solved
to few possibilities but then adding extra variables,
constraints or combining with another disjoint problem
"""
# pylint:disable=invalid-name
# pyright: reportMissingModuleSource=false
# pyright: reportMissingImports=false
# pylint:disable=import-error
from collections.abc import Hashable
from typing import (
    Any, Callable, Dict,
    Iterable, Iterator,
    List, Optional, Sequence, Set, Tuple, Union
)
from itertools import chain,product,starmap
from constraint import Problem,Constraint,FunctionConstraint,Solver,Domain

VarType = Hashable
CommonDomainType = Any
SolutionType = Dict[VarType,CommonDomainType]
ConstraintType = Union[Constraint,Callable]
ConstraintVarsType = Union[Set[VarType],Sequence[VarType]]
DomainType = Union[List,tuple,"Domain"]

class ProblemCached(Problem):
    """
    similar to problem from constraint
    """
    def __init__(self, solver:Solver = None):
        super().__init__(solver=solver)
        self.clearSolutions()
    def clearSolutions(self) -> None:
        """clear"""
        self.solutions_iterator : Iterator[SolutionType] = ({} for _ in range(0))
        self.solutions_iterated : List[SolutionType] = []
        self.resolve = True
    def reset(self) -> None:
        """clear along with Problem reset"""
        super().reset()
        self.clearSolutions()
    def setSolver(self, solver:Solver) -> None:
        """set a solver"""
        super().setSolver(solver)
        self.clearSolutions()
    def addVariable(self,variable:VarType,domain:DomainType) -> None:
        """add an unconstrained variable with specified name and domain"""
        super().addVariable(variable,domain)
        if self.resolve:
            self.clearSolutions()
        else:
            def bind(iterator:Iterable[SolutionType],
                new_variable:VarType,
                new_domain:"Domain") -> Iterator[SolutionType]:
                """new solutions are old solutions along with
                new_variable being anything possible from new_domain"""
                for solution in iterator:
                    for domain_elt in new_domain:
                        solution[new_variable] = domain_elt
                        yield solution
            domain_instance : "Domain" = self._variables[variable]
            # pylint:disable=attribute-defined-outside-init
            self.solutions_iterator = bind(self.solutions_iterator,variable,domain_instance)
            self.solutions_iterated = list(bind(self.solutions_iterated,variable,domain_instance))
    def addVariables(self, variables:Iterable[VarType], domain:DomainType) -> None:
        """add multiple unconstrained variables, all with the same domain"""
        for variable in variables:
            self.addVariable(variable, domain)
    def addConstraint(self,constraint:ConstraintType,
        variables:Optional[ConstraintVarsType]=None) -> None:
        """add a constraint on some variables"""
        if not isinstance(constraint, Constraint):
            if callable(constraint):
                true_constraint = FunctionConstraint(constraint)
            else:
                msg = "Constraints must be instances of subclasses of the Constraint class"
                raise ValueError(msg)
        else:
            true_constraint = constraint
        super().addConstraint(true_constraint,variables)
        if self.resolve:
            self.clearSolutions()
        else:
            if variables is None:
                domains = self._variables.copy()
                my_variables = domains.keys()
                my_domains = domains.values()
            else:
                my_variables = variables
                my_domains = [self._variables[var] for var in variables]
            # pylint:disable=attribute-defined-outside-init
            self.solutions_iterator = filter(lambda sol: true_constraint(my_variables,
                my_domains,sol),self.solutions_iterator)
            self.solutions_iterated = [sol for sol in self.solutions_iterated
                if true_constraint(my_variables,my_domains,sol)]
    def getSolution(self) -> Optional[SolutionType]:
        """get the next solution"""
        if self.resolve:
            self.clearSolutions()
            return super().getSolution()
        fresh_solution = next(self.solutions_iterator, None)
        if fresh_solution is not None:
            self.solutions_iterated.append(fresh_solution)
            return fresh_solution.copy()
        if self.solutions_iterated:
            return self.solutions_iterated[0].copy()
        return None
    def getSolutions(self) -> List[SolutionType]:
        """get all the solutions"""
        if self.resolve:
            all_sols=super().getSolutions()
        else:
            all_sols = list(self.getSolutionIter())
        # pylint:disable=attribute-defined-outside-init
        self.solutions_iterated = all_sols
        self.solutions_iterator = ({} for _ in range(0))
        self.resolve = False
        return all_sols
    def makeSolutionIter(self) -> None:
        """don't re-solve anymore and keep the iterator"""
        if self.resolve:
            all_sols_iter=super().getSolutionIter()
            # pylint:disable=attribute-defined-outside-init
            self.solutions_iterated = []
            self.solutions_iterator = all_sols_iter
            self.resolve = False
    def getSolutionIter(self) -> Iterator[SolutionType]:
        """return the iterator"""
        if self.resolve:
            all_sols_iter=super().getSolutionIter()
        else:
            all_sols_iter = chain(self.solutions_iterated,self.solutions_iterator)
        self.clearSolutions()
        return all_sols_iter
    def combine_problems(self,other:"ProblemCached",both_small:bool=False) -> None:
        """two disjoint problems"""
        selfdomains = self._variables
        selfallvariables = selfdomains.keys()
        otherdomains = other._variables # pylint:disable=protected-access
        otherallvariables = otherdomains.keys()
        overlap = False
        for selfvar in selfallvariables:
            if selfvar in otherallvariables:
                overlap = True
                break
        if overlap:
            raise ValueError("The variables involved in the two problems must be disjoint")
        for othervar in otherallvariables:
            super().addVariable(othervar,otherdomains[othervar].copy())
        # pylint:disable=protected-access
        for otherconstraint,otherconstraintvariables in other._constraints:
            if not otherconstraintvariables:
                super().addConstraint(otherconstraint)
            else:
                super().addConstraint(otherconstraint,otherconstraintvariables)
        if self.resolve or other.resolve or not both_small:
            self.clearSolutions()
        else:
            self_reset_iterator = chain(self.solutions_iterated,self.solutions_iterator)
            other_reset_iterator = chain(other.solutions_iterated,other.solutions_iterator)
            # pylint:disable=attribute-defined-outside-init
            self.resolve = False
            self.solutions_iterator = starmap(lambda dict1,dict2: {**dict1, **dict2},
                product(self_reset_iterator,other_reset_iterator))
            self.solutions_iterated = []
            other.clearSolutions()
    def loosely_couple(self,other:"ProblemCached",
        both_small:bool,
        cross_constraint_list : List[Tuple[ConstraintType,Optional[ConstraintVarsType]]]) -> None:
        """only a few constraints that cut across both problems"""
        self_nonempty = len(self._variables)>0
        # pylint:disable=protected-access
        other_nonempty = len(other._variables)>0
        for _,variables in cross_constraint_list:
            if variables is not None:
                overlaps_self = any((var in self._variables for var in variables))
                overlaps_other = any((var in other._variables for var in variables))
            else:
                overlaps_self = self_nonempty
                overlaps_other = other_nonempty
            cross_cutting = overlaps_self and overlaps_other
            if not cross_cutting:
                raise ValueError("""The variables for cross cutting constraints
                    must overlap with the variables of both the two problems""")
        self.combine_problems(other,both_small)
        for constraint,variables in cross_constraint_list:
            self.addConstraint(constraint,variables)
