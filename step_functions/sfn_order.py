from z3 import *
from dataclasses import dataclass, field
from typing import Any, Dict, Union
from itertools import groupby

StepName = Union[
    'Start',
    'ResumeNgmScaling',
    'UpdateInternalState',
    'Something',
    'CreateDbCluster',
    'CheckDbStatus',
    'IsThings',
    'Dummy1',
    'Dummy2',
    'Dummy3',
    'Terminal',
]

@dataclass
class Spec():
    step_position: Any
    pass

SpecDefinition = Dict[StepName, Spec]

@dataclass
class StepSpec(Spec):
    subsequent_steps: List[StepName]
    is_condition_terminal: bool = False
    steps_dependent_on_parent_step: List[StepName] = field(default_factory=list)

@dataclass
class ConditionalStepSpec(Spec):
    branch1: SpecDefinition
    branch2: SpecDefinition

# move to a JSON spec
SPEC: SpecDefinition = {
    'ResumeNgmScaling': StepSpec(
        subsequent_steps = ['UpdateInternalState'],
        step_position = Int('ResumeNgmScaling'),
    ),
    'CreateDbCluster': StepSpec(
        subsequent_steps = ['CheckDbStatus'],
        step_position = Int('CreateDbCluster'),
    ),
    'Something': StepSpec(
        subsequent_steps = ['UpdateInternalState'],
        step_position = Int('Something'),
    ),
    'UpdateInternalState': StepSpec(
        subsequent_steps = ['IsThings'],
        step_position = Int('UpdateInternalState'),
    ),
    'CheckDbStatus': StepSpec(
        subsequent_steps = ['IsThings'],
        step_position = Int('CheckDbStatus'),
    ),
    'IsThings': ConditionalStepSpec(
        branch1 = {
            'Dummy1': StepSpec(
                subsequent_steps = ['Dummy3'],
                step_position = Int('Dummy1'),
            ),
            'Dummy3': StepSpec(
                subsequent_steps = ['Terminal'],
                step_position = Int('Dummy3'),
            ),
        },
        branch2 = {
            'Dummy2': StepSpec(
                subsequent_steps = ['Terminal'],
                step_position = Int('Dummy2'),
            ),
        },
        step_position = Int('IsThings'),
    ),
    'Terminal': StepSpec(
        subsequent_steps = [],
        step_position = Int('Terminal'),
    ),
}

###### Z3 implemention starts here ######

@dataclass
class StepTreeNode():
    pass

@dataclass
class Step(StepTreeNode):
    step_name: str

@dataclass
class StepSequence(StepTreeNode):
    sequence: List[StepTreeNode]

@dataclass
class StepParallel(StepTreeNode):
    parallel_steps: List[StepTreeNode]

def to_tree(chain):
    if isinstance(chain, str):
        return Step(chain)

    def convert(node):
        if len(node) == 1:
            return Step(node[0])
        else:
            return StepParallel([to_tree(step) for step in node])

    return StepSequence([convert(node) for node in chain])

def pretty_print(tree):
    if isinstance(tree, StepSequence):
        return f'(seq {' '.join([pretty_print(step) for step in tree.sequence])})'
    elif isinstance(tree, Step):
        return tree.step_name
    elif isinstance(tree, StepParallel):
        return f'(parallel {' '.join([pretty_print(step) for step in tree.parallel_steps])})'
    else:
        return ''

s = Optimize()

SPEC['Start'] = StepSpec(
    subsequent_steps = list(SPEC.keys()),
    step_position = Int('Start'),
)
s.add(SPEC['Start'].step_position == 1)

for name, spec in SPEC.items():
    if isinstance(spec, StepSpec):
        for step in spec.subsequent_steps:
            s.add(spec.step_position < SPEC[step].step_position)
    # this needs to be done recursively
    elif isinstance(spec, ConditionalStepSpec):
        pass
        # for  in spec.branch1.items().subsequent_steps:
        #     s.add(spec.step_position < SPEC[step].step_position)
        # for step in spec.branch2.subsequent_steps:
        #     s.add(spec.step_position < SPEC[step].step_position)

    s.add(spec.step_position >= 1)
    s.add(spec.step_position <= len(SPEC))
    s.minimize(spec.step_position)

# optimize the distance between latency dependent steps
s.maximize(SPEC['CheckDbStatus'].step_position - SPEC['CreateDbCluster'].step_position)

if s.check() == sat:
    m = s.model()

    name_to_position = { name: m[spec.step_position].as_long() for name, spec in SPEC.items() }
    dependency_chain = sorted(name_to_position.items(), key=lambda item: item[1])
    grouped_chain = groupby(dependency_chain, lambda s1: s1[1])

    tree = to_tree([[s[0] for s in g] for _, g in grouped_chain])
    print(pretty_print(tree))
else:
    print('no satisfying assignment. :(')
