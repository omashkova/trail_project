import pandas as pd
import os
from axiom_parser import modify
import re

def generate_result_file(ontology, path_to_tptp):
    all_classes = list(ontology.getClassesInSignature())
    result = pd.DataFrame(columns=['problem_name', 'conjecture', 'difficulty', 'max_time'])
    for filename in os.listdir(os.path.join(path_to_tptp, 'Problems/TPTP/')):
        if filename.endswith('p'):
            new_row = {k: None for k in result.columns}
            new_row['problem_name'] = filename
            splitted = re.split('_|.p', filename)
            i = eval(splitted[-2])
            C = modify(all_classes[i])
            formula = f'! [X] : ( {C}(X) => (a(X) & ~ (a(X)) ) )'
            fof_string = f'fof(unsat_axiom, conjecture, {formula} ).'
            new_row['conjecture'] = fof_string
            new_row['difficulty'] = 0
            new_row['max_time'] = 1
            result = result.append(new_row, ignore_index=True)
    result.to_csv(os.path.join(path_to_tptp, 'Problems/result.tsv'), index=False, header=False, sep='\t')