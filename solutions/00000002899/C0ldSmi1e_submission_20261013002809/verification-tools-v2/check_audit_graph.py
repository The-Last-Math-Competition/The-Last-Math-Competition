#!/usr/bin/env python3
"""Independently recompute exported dependency-graph closure and trust summaries."""
import collections,json,pathlib,sys
p=pathlib.Path(sys.argv[1]);data=json.loads(p.read_text())
graph={r['name']:r for r in data['dependency_graph']}
assert len(graph)==len(data['dependency_graph'])==data['closure_declaration_count']
roots={r['name']:r for r in data['declarations']}
assert len(roots)==len(data['declarations'])==data['local_declaration_count']
assert data['kernel_check_performed'] is False
assert data['strict_dependency_policy'] is True
assert not data['failures']
union=set()
for name,root in roots.items():
    seen=set();pending=[name]
    while pending:
        current=pending.pop()
        if current in seen:continue
        seen.add(current)
        node=graph[current]
        if root['trust_enforced']: assert node['kind']!='unavailable'
        edges=set(node['type_dependencies'])|set(node['body_dependencies'])|set(node['recursor_dependencies'])|set(node['inductive_dependencies'])
        assert edges==set(node['dependencies'])
        pending.extend(edges-seen)
    assert seen==set(root['closure']),name
    axioms={n for n in seen if graph[n]['kind']=='axiom'}
    unsafe={n for n in seen if graph[n]['unsafe']}
    assert axioms==set(root['axioms']),name
    assert unsafe==set(root['unsafe_dependencies']),name
    assert set(root['lean_collectAxioms'])<=axioms,name
    if root['trust_enforced']:
        assert axioms<=set(data['permitted_axioms']) and not unsafe,name
    union |= seen
assert union==set(graph)
counts=collections.Counter(r['module'] for r in roots.values())
for row in data['module_counts']: assert row['declarations']==counts[row['module']]
print(json.dumps({'status':'PASS','roots':len(roots),'graph_nodes':len(graph),'module_counts':dict(counts),'scope':'Internal graph/closure/trust consistency; not an independent Lean environment extraction or kernel recheck.'},indent=2))
