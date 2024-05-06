import mowl
mowl.init_jvm("10g", "1g", 8)

from mowl.owlapi import OWLAPIAdapter
from org.semanticweb.elk.owlapi import ElkReasonerFactory
from mowl.datasets import PathDataset
from com.clarkparsia.owlapi.explanation import BlackBoxExplanation
from com.clarkparsia.owlapi.explanation import HSTExplanationGenerator
from org.semanticweb.owlapi.model import IRI
import os
import pandas as pd

def generate_explanations(ontology_path, explanation_path):

    ontology = PathDataset(ontology_path).ontology
    
    reasoner_factory = ElkReasonerFactory()
    reasoner = reasoner_factory.createReasoner(ontology)
    
    unsatisfiable_cl = list(reasoner.getUnsatisfiableClasses())
    
    bbe = BlackBoxExplanation(ontology, reasoner_factory, reasoner)
    hsteg = HSTExplanationGenerator(bbe)
    
    result = pd.DataFrame(columns=['class_name', 'file_name'])
    
    adapter = OWLAPIAdapter()
    manager = adapter.owl_manager
    
    for i in range(len(unsatisfiable_cl)):
        ax_set = hsteg.getExplanations(unsatisfiable_cl[i], 1)
        print(f'Got explanations for class number {i}')
        explanation = adapter.create_ontology(f"http://explanation_{i}")
        for ax in ax_set:
            for axx in list(ax):
                manager.addAxiom(explanation, axx)
        manager.saveOntology(explanation, IRI.create("file://" + os.path.join(explanation_path, "explanation"+f"_{str(i)}"+".owl")))
        new_row = {k: None for k in result.columns}
        new_row['file_name'] = f"explanation_{i}.owl"
        new_row['class_name'] = str(unsatisfiable_cl[i])
        result = result.append(new_row, ignore_index=True)
    result.to_csv(os.path.join(explanation_path, 'explanations.csv'), index=False, header=True)