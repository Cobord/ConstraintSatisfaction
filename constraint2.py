from typing import Any, Callable, Dict, Hashable, Iterable, Iterator, List, Optional, Sequence, Set, Tuple, Union
from constraint import Problem,Constraint,FunctionConstraint,Solver,Domain
from itertools import chain,product,starmap

VarType = Hashable
CommonDomainType = Any
SolutionType = Dict[VarType,CommonDomainType]
ConstraintType = Union[Constraint,Callable]
ConstraintVarsType = Union[Set[VarType],Sequence[VarType]]
DomainType = Union[List,tuple,"Domain"]

class ProblemCached(Problem):
    def __init__(self, solver:Solver = None):
        super().__init__(solver=solver)
        self.clearSolutions()
    def clearSolutions(self) -> None:
        self.solutions_iterator : Iterator[SolutionType] = ({} for _ in range(1) if False)
        self.solutions_iterated : List[SolutionType] = []
        self.resolve = True
    def reset(self) -> None:
        super().reset()
        self.clearSolutions()
    def setSolver(self, solver:Solver) -> None:
        super().setSolver(solver)
        self.clearSolutions()
    def addVariable(self,variable:VarType,domain:DomainType) -> None:
        super().addVariable(variable,domain)
        if self.resolve:
            self.clearSolutions()
        else:
            def bind(iterator:Iterable[SolutionType],new_variable:VarType,new_domain:"Domain") -> Iterator[SolutionType]:
                for solution in iterator:
                    for domain_elt in new_domain:
                        solution[new_variable] = domain_elt
                        yield solution
            domain_instance : "Domain" = self._variables[variable]
            self.solutions_iterator = bind(self.solutions_iterator,variable,domain_instance)
            self.solutions_iterated = list(bind(self.solutions_iterated,variable,domain_instance))
    def addVariables(self, variables:Iterable[VarType], domain:DomainType) -> None:
        for variable in variables:
            self.addVariable(variable, domain)
    def addConstraint(self,constraint:ConstraintType,variables:Optional[ConstraintVarsType]=None) -> None:
        if not isinstance(constraint, Constraint):
            if callable(constraint):
                true_constraint = FunctionConstraint(constraint)
            else:
                msg = "Constraints must be instances of subclasses " "of the Constraint class"
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
            self.solutions_iterator = filter(lambda sol: true_constraint(my_variables,my_domains,sol),self.solutions_iterator)
            self.solutions_iterated = [sol for sol in self.solutions_iterated if true_constraint(my_variables,my_domains,sol)]
    def getSolution(self) -> Optional[SolutionType]:
        if self.resolve:
            self.clearSolutions()
            return super().getSolution()
        else:
            fresh_solution = next(self.solutions_iterator, None)
            if fresh_solution is not None:
                self.solutions_iterated.append(fresh_solution)
                return fresh_solution.copy()
            else:
                if self.solutions_iterated:
                    return self.solutions_iterated[0].copy()
                else:
                    return None
    def getSolutions(self) -> List[SolutionType]:
        if self.resolve:
            all_sols=super().getSolutions()
        else:
            all_sols = list(self.getSolutionIter())
        self.solutions_iterated = all_sols
        self.solutions_iterator = ({} for _ in range(1) if False)
        self.resolve = False
        return all_sols
    def makeSolutionIter(self) -> None:
        if self.resolve:
            all_sols_iter=super().getSolutionIter()
            self.solutions_iterated = []
            self.solutions_iterator = all_sols_iter
            self.resolve = False
    def getSolutionIter(self) -> Iterator[SolutionType]:
        if self.resolve:
            all_sols_iter=super().getSolutionIter()
        else:
            all_sols_iter = chain(self.solutions_iterated,self.solutions_iterator)
        self.clearSolutions()
        return all_sols_iter
    def combine_problems(self,other:"ProblemCached",both_small:bool=False) -> None:
        selfdomains = self._variables
        selfallvariables = selfdomains.keys()
        otherdomains = other._variables
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
        for otherconstraint,otherconstraintvariables in other._constraints:
            if not otherconstraintvariables:
                super().addConstraint(otherconstraint)
            else:
                super().addConstraint(otherconstraint,otherconstraintvariables)
        if self.resolve or other.resolve or not(both_small):
            self.clearSolutions()
        else:
            self.resolve = False
            self_reset_iterator = chain(self.solutions_iterated,self.solutions_iterator)
            other_reset_iterator = chain(other.solutions_iterated,other.solutions_iterator)
            self.solutions_iterator = starmap(lambda dict1,dict2: {**dict1, **dict2},product(self_reset_iterator,other_reset_iterator))
            self.solutions_iterated = []
            other.clearSolutions()
    def loosely_couple(self,other:"ProblemCached",both_small:bool,cross_constraint_list : List[Tuple[ConstraintType,Optional[ConstraintVarsType]]]) -> None:
        self_nonempty = len(self._variables)>0
        other_nonempty = len(other._variables)>0
        for _,variables in cross_constraint_list:
            if variables is not None:
                overlaps_self = any([var in self._variables for var in variables])
                overlaps_other = any([var in other._variables for var in variables])
            else:
                overlaps_self = self_nonempty
                overlaps_other = other_nonempty
            cross_cutting = overlaps_self and overlaps_other
            if not cross_cutting:
                raise ValueError("The variables for cross cutting constraints must overlap with the variables of both the two problems")
        self.combine_problems(other,both_small)
        for constraint,variables in cross_constraint_list:
            self.addConstraint(constraint,variables)