import re
import regex

def modify(cl):
    str_cl = str(cl).replace('/', '_')
    str_cl = str_cl.replace(':', '')
    str_cl = str_cl.replace('.', '_')
    str_cl = str_cl.replace('#', '_')
    str_cl = str_cl.replace('?', '_')
    str_cl = str_cl.replace('=', '_')
    str_cl = str_cl.replace('-', '_')
    str_cl = str_cl.replace('+', '_')
    return str_cl[1:-1]

def axiom_parser(ax, variables, i, rel=False, second_arg=None, refl=False):
    if ax == "owl:Thing":
        return f"(a({variables[i]}) | ~ (a({variables[i]})))"
    if ax == "owl:Nothing":
        return f"(a({variables[i]}) & ~ (a({variables[i]})))"
    if ax.startswith('<'):
        if not rel:
            return f"{modify(ax)}({variables[i]})"
        else:
            if second_arg is None:
                if not refl:
                    return f"{modify(ax)}({variables[i]}, {variables[i + 1]})", i + 1
                else:
                    return f"{modify(ax)}({variables[i]}, {variables[i]})", i
            else:
                return f"{modify(ax)}({variables[i]}, {variables[second_arg]})", second_arg
    if ax.startswith('SubClassOf'):
        str_ax = re.split("SubClassOf\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2, str(ax)
        left_part = axiom_parser(matches[0], variables, i)
        right_part = axiom_parser(matches[1], variables, i)
        return f"! [{variables[i]}] : ( {left_part} => {right_part} )"
    if ax.startswith('ClassAssertion'):
        str_ax = re.split("ClassAssertion[(]| |[)]", ax)
        str_ax = [elem for elem in str_ax if elem != '']
        return f"{modify(str_ax[0])}({modify(str_ax[1])})"
    if ax.startswith('ObjectPropertyAssertion'):
        str_ax = re.split("ObjectPropertyAssertion[(]| |[)]", ax)
        str_ax = [elem for elem in str_ax if elem != '']
        return f"{modify(str_ax[0])}({modify(str_ax[1])}, {modify(str_ax[1])})"
    if ax.startswith('ObjectSomeValuesFrom'):
        str_ax = re.split("ObjectSomeValuesFrom\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2
        left_part, last_var_ix = axiom_parser(matches[0], variables, i, rel=True)
        right_part = axiom_parser(matches[1], variables, last_var_ix)
        return f"( ? [{variables[last_var_ix]}] : ( {left_part} & {right_part} ) )"
    if ax.startswith('ObjectIntersectionOf'):
        str_ax = re.split("ObjectIntersectionOf\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        formula = ''
        for elem in matches:
            one_part = axiom_parser(elem, variables, i)
            formula += one_part
            formula += ' & '
        formula = formula[:-2]
        return f"( {formula} )"
    if ax.startswith('SubObjectPropertyOf'):
        str_ax = re.split("SubObjectPropertyOf\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2
        if matches[0].startswith('<'):
            left_part, last_var_ix = axiom_parser(matches[0], variables, i, rel=True)
        else:
            left_part, last_var_ix = axiom_parser(matches[0], variables, i)
        right_part, second_last_arg = axiom_parser(matches[1], variables, i, second_arg=last_var_ix, rel=True)
        k = i
        var_part = ''
        while k <= second_last_arg:
            var_part += f'{variables[k]}, '
            k += 1
        var_part = var_part[:-2]
        return f"! [{var_part}] : ( {left_part} => {right_part} )"
    if ax.startswith('EquivalentObjectProperties'):
        str_ax = re.split("EquivalentObjectProperties\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2
        if matches[0].startswith('<'):
            left_part, last_var_ix = axiom_parser(matches[0], variables, i, rel=True)
        else:
            left_part, last_var_ix = axiom_parser(matches[0], variables, i)
        right_part, second_last_arg = axiom_parser(matches[1], variables, i, second_arg=last_var_ix, rel=True)
        k = i
        var_part = ''
        while k <= second_last_arg:
            var_part += f'{variables[k]}, '
            k += 1
        var_part = var_part[:-2]
        return f"! [{var_part}] : ( {left_part} <=> {right_part} )"
    if ax.startswith('ObjectPropertyChain'):
        str_ax = re.split("ObjectPropertyChain\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        formula = ''
        k = i
        for elem in matches:
            one_part, last_var_ix = axiom_parser(elem, variables, k, rel=True)
            k = last_var_ix
            formula += one_part
            formula += ' & '
        formula = formula[:-2]
        return f"( {formula} )", last_var_ix
    if ax.startswith('ObjectPropertyDomain'):
        str_ax = re.split("ObjectPropertyDomain\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2
        left_part, last_ix = axiom_parser(matches[0], variables, i, rel=True)
        right_part = axiom_parser(matches[1], variables, i)
        return f"! [{variables[i]}, {variables[last_ix]}] : ( {left_part} => {right_part} )"
    if ax.startswith('ObjectPropertyRange'):
        str_ax = re.split("ObjectPropertyRange\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2
        left_part, last_ix = axiom_parser(matches[0], variables, i, rel=True)
        right_part = axiom_parser(matches[1], variables, last_ix)
        return f"! [{variables[i]}, {variables[last_ix]}] : ( {left_part} => {right_part} )"
    if ax.startswith('TransitiveObjectProperty'):
        str_ax = re.split("TransitiveObjectProperty\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        first_part, first_ix = axiom_parser(matches[0], variables, i, rel=True)
        second_part, second_ix = axiom_parser(matches[0], variables, first_ix, rel=True)
        third_part, _ = axiom_parser(matches[0], variables, i, second_arg=second_ix, rel=True)
        return f"! [{variables[i]}, {variables[first_ix]}, {variables[second_ix]}] : ( ( {first_part} & {second_part} ) => {third_part} )"
    if ax.startswith('SymmetricObjectProperty'):
        str_ax = re.split("SymmetricObjectProperty\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        first_part, first_ix = axiom_parser(matches[0], variables, i, rel=True)
        second_part, _ = axiom_parser(matches[0], variables, first_ix, second_arg=i, rel=True)
        return f"! [{variables[i]}, {variables[first_ix]}] : ( ( {first_part} ) <=> ( {second_part} ) )"
    if ax.startswith('AsymmetricObjectProperty'):
        str_ax = re.split("AsymmetricObjectProperty\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        first_part, first_ix = axiom_parser(matches[0], variables, i, rel=True)
        second_part, _ = axiom_parser(matches[0], variables, first_ix, second_arg=i, rel=True)
        return f"! [{variables[i]}, {variables[first_ix]}] : ( ( {first_part} ) <=> ( ~ ({second_part}) ) )"
    if ax.startswith('DisjointClasses'):
        str_ax = re.split("DisjointClasses\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        formula = ''
        for elem in matches:
            one_part = axiom_parser(elem, variables, i)
            formula += one_part
            formula += ' & '
        formula = formula[:-2]
        return f"! [{variables[i]}] : ( ( {formula} ) => (a({variables[i]}) & ~ (a({variables[i]}) ) ) )"
    if ax.startswith("InverseObjectProperties"):
        str_ax = re.split("InverseObjectProperties\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2
        left_part, first_ix = axiom_parser(matches[0], variables, i, rel=True)
        right_part, _ = axiom_parser(matches[1], variables, first_ix, second_arg=i, rel=True)
        return f"! [{variables[i]}, {variables[first_ix]}] : ( {left_part} <=> {right_part} )"
    if ax.startswith("ObjectUnionOf"):
        str_ax = re.split("ObjectUnionOf\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        formula = ''
        for elem in matches:
            one_part = axiom_parser(elem, variables, i)
            formula += one_part
            formula += ' | '
        formula = formula[:-2]
        return f"( {formula} )"
    if ax.startswith('ObjectAllValuesFrom'):
        str_ax = re.split("ObjectAllValuesFrom\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2
        left_part, last_var_ix = axiom_parser(matches[0], variables, i, rel=True)
        right_part = axiom_parser(matches[1], variables, last_var_ix)
        return f"( ! [{variables[last_var_ix]}] : ( {left_part} => {right_part} ) )"
    if ax.startswith('EquivalentClasses'):
        str_ax = re.split("EquivalentClasses\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 2, str(ax)
        left_part = axiom_parser(matches[0], variables, i)
        right_part = axiom_parser(matches[1], variables, i)
        return f"! [{variables[i]}] : ( {left_part} <=> {right_part} )"
    if ax.startswith('ObjectComplementOf'):
        str_ax = re.split("ObjectComplementOf\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        left_part = axiom_parser(matches[0], variables, i)
        return f"( ~ ({left_part}) )"
    if ax.startswith('IrreflexiveObjectProperty'):
        str_ax = re.split("IrreflexiveObjectProperty\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        first_part, first_ix = axiom_parser(matches[0], variables, i, rel=True, refl=True)
        return f"! [{variables[i]}] : ( ( ~ ({first_part}) ) )"
    if ax.startswith('ReflexiveObjectProperty'):
        str_ax = re.split("ReflexiveObjectProperty\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        first_part, first_ix = axiom_parser(matches[0], variables, i, rel=True, refl=True)
        return f"! [{variables[i]}] : ( ( {first_part} ) )"
    if ax.startswith('FunctionalObjectProperty'):
        str_ax = re.split("FunctionalObjectProperty\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        first_part, first_ix = axiom_parser(matches[0], variables, i, rel=True)
        second_part, _ = axiom_parser(matches[0], variables, i, second_arg=first_ix+1, rel=True)
        return f"! [{variables[i]}, {variables[first_ix]}, {variables[first_ix+1]}] : ( ( ( {first_part} ) & ({second_part}) ) => ( {variables[first_ix]} = {variables[first_ix+1]} ) )"
    if ax.startswith('InverseFunctionalObjectProperty'):
        str_ax = re.split("InverseFunctionalObjectProperty\((.*)\)", ax)
        str_ax = [elem for elem in str_ax if elem != ''][0]
        matches = [match.group() for match in regex.finditer(r"(?:(\((?>[^()]+|(?1))*\))|\S)+", str_ax)]
        assert len(matches) == 1
        first_part, first_ix = axiom_parser(matches[0], variables, i, rel=True)
        second_part, _ = axiom_parser(matches[0], variables, first_ix+1, second_arg=first_ix, rel=True)
        return f"! [{variables[i]}, {variables[first_ix]}, {variables[first_ix+1]}] : ( ( ( {first_part} ) & ({second_part}) ) => ( {variables[i]} = {variables[first_ix+1]} ) )"
    if str(ax).startswith('DLSafeRule'):
        if 'Nothing' in str(ax):
            print('DL rule with Nothing:')
            print(str(ax))
        str_ax = re.split("DLSafeRule|\(| |\)", str(ax))
        str_ax = [elem for elem in str_ax if elem != ""]
        variables_ = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 
                     'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z']
        var_ix = 0
        var_dict = {}
        i = 0
        head_i = 0
        head_flag = False
        while i < len(str_ax):
            if str_ax[i] == 'Body':
                formula = '('
                i += 1
            elif str_ax[i] == 'ObjectPropertyAtom':
                R = modify(str_ax[i+1])
                var1 = str_ax[i+3]
                var2 = str_ax[i+5]
                if var1 not in var_dict.keys():
                    var_dict[var1] = variables_[var_ix]
                    var_ix += 1
                if var2 not in var_dict.keys():
                    var_dict[var2] = variables_[var_ix]
                    var_ix += 1
                if i == 1 or head_flag:
                    formula += f'{R}({var_dict[var1]}, {var_dict[var2]}) '
                elif i > 1 and not head_flag:
                    formula += f'& {R}({var_dict[var1]}, {var_dict[var2]}) '
                i += 6
            elif str_ax[i] == 'ClassAtom':
                if 'Nothing' not in str_ax[i+1]: # owl:Nothing
                    C = modify(str_ax[i+1])
                    var1 = str_ax[i+3]
                    if var1 not in var_dict.keys():
                        var_dict[var1] = variables_[var_ix]
                        var_ix += 1
                    if i == 1:
                        formula += f'{C}({var_dict[var1]}) '
                    else:
                        formula += f'& {C}({var_dict[var1]}) '
                    i += 4
                else:
                    C = 'a'
                    var1 = str_ax[i+3]
                    if var1 not in var_dict.keys():
                        var_dict[var1] = variables_[var_ix]
                        var_ix += 1
                    if i == 1 or head_i == 1:
                        formula += f'({C}({var_dict[var1]}) & ~ ({C}({var_dict[var1]}))) '
                        head_i += 1
                    else:
                        formula += f'& ({C}({var_dict[var1]}) & ~ ({C}({var_dict[var1]}))) '
                    i += 4
            elif str_ax[i] == 'Head':
                formula += ') => ('
                i += 1
                head_flag = True
                head_i += 1
        formula += ') )'
        start = '! ['
        start += ', '.join(list(var_dict.values()))
        start += ']: ('
        formula = start + formula
        return formula
    else:
        print(ax)
        print('======')

variables = ['X', 'Y', 'Z', 'W', 'V', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 
             'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 
             'T', 'U', 'AA', 'AB', 'AC', 'AD', 'AE', 'AF', 'AG', 'AH', 
             'AI']
def onto_to_tptp_2(ontology, path_to_tptp, i):
    f = open(path_to_tptp, 'w')
    count = 0
    for ax in ontology.getAxioms():
        if str(ax).startswith('Declaration(Class('):
            continue
        if str(ax).startswith('DifferentIndividuals'):
            continue
        if str(ax).startswith('Declaration(ObjectProperty('):
            continue
        if str(ax).startswith('SameIndividual'):
            continue
        if 'ObjectOneOf' in str(ax):
            continue
        if 'ObjectExactCardinality' in str(ax):
            continue
        if 'DataPropertyRange' in str(ax):
            continue
        if 'ObjectMinCardinality' in str(ax):
            continue
        if 'DataPropertyDomain' in str(ax):
            continue
        if 'DataPropertyAssertion' in str(ax):
            continue
        if 'DataHasValue' in str(ax):
            continue
        if str(ax).startswith('Declaration(DataProperty('):
            continue
        if 'ObjectHasValue' in str(ax):
            continue
        if 'DataExactCardinality' in str(ax):
            continue
        if 'EquivalentDataProperties' in str(ax):
            continue
        if 'owl:topObjectProperty' in str(ax):
            continue
        if 'FunctionalDataProperty' in str(ax):
            continue
        if 'DataSomeValuesFrom' in str(ax):
            continue
        if 'ObjectMaxCardinality' in str(ax):
            continue
        if 'DataMaxCardinality' in str(ax):
            continue
        if 'SubDataPropertyOf' in str(ax):
            continue
        if 'DataMinCardinality' in str(ax):
            continue
        if 'ObjectInverseOf' in str(ax):
            continue
        if 'Annotation' in str(ax):
            continue
        if 'DataAllValuesFrom' in str(ax):
            continue
        if 'ObjectHasSelf' in str(ax):
            continue
        if 'Declaration(NamedIndividual' in str(ax):
            continue
        else:
            formula = axiom_parser(str(ax), variables, 0)
            fof_string = f'fof(axiom_{count}, axiom, {formula} ).'
            count += 1
            f.write(fof_string)
            f.write('\n')
    # add a conjecture
    all_classes = list(ontology.getClassesInSignature())
    C = modify(all_classes[i])
    # C = modify(pd.read_csv('ore_ontology_13242/explanations/explanations.csv')['class_name'].iloc[i])
    # C = modify('<http://my_class>')
    formula = f'! [X] : ( {C}(X) => (a(X) & ~ (a(X)) ) )'
    fof_string = f'fof(unsatisfiability_conjecture, conjecture, {formula} ).'
    f.write(fof_string)
    f.write('\n')
    f.close()