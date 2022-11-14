# Part of the code borrowed from Plankton and Ali. 

# class FattreeTopo():
#  	def __init__(self, k):
# 		self.cores = (k/2)**2
# 		self.aggs = (k/2) * k
# 	    self.edges = (k/2) * k
# 	    self.hosts = (k/2)**2 * k
	   
# 	def generate_topo():

import networkx as nx

def generate_fattree(k):
	if k % 2 != 0:
		raise ValueError('"k" has to be even')

	G = nx.Graph()

	## Nodes/Switches
	# G.add_nodes(range(0, (k / 2) ** 2 + k ** 2))
	index = 0
	core_switches = range(index, index + (k // 2) ** 2)
	index += len(core_switches)
	agg_switches = range(index, index + (k ** 2) // 2)
	index += len(agg_switches)
	edge_switches = range(index, index + (k ** 2) // 2)
	index += len(edge_switches)
	hosts = range(index, index + (k ** 2))
	#index += len(hosts)
	print(edge_switches)
	print(hosts)

	## Core-Aggregation Links
	for i, core in enumerate(core_switches):
		for j in range(0, k):
			agg = agg_switches[j * (k // 2) + i // (k // 2)]
			G.add_edge(core, agg)
			G.add_edge(agg, core)

	## Aggregation-Edge Links
	for i, agg in enumerate(agg_switches):
		for j in range(0, k // 2):
			edge = edge_switches[(i - i % (k // 2)) + j]
			G.add_edge(agg, edge)
			G.add_edge(edge, agg)

	## Host-Edge Links
	for i, edge in enumerate(edge_switches):
		for j in range(0, 2):
			host = hosts[j + i * 2]
			#print(host)
			G.add_edge(host, edge)
			G.add_edge(edge, host)

	return G, core_switches, edge_switches, hosts


def add_to_path(h, stack, paths):
	if h not in paths:
		paths[h] = []
	paths[h].append(stack.copy())

def dfs_path(G, stack, hosts, paths):
	cur = stack[-1]
	for m in G[cur]:
		if m in hosts:
			add_to_path(m, stack, paths)
		elif m not in stack:
			stack.append(m)
			dfs_path(G, stack, hosts, paths)
			stack.pop()
			#visited[m].add(m)

def generate_edge_id(edge_id, G):
	index = 0

	for e in G.edges():
		e0 = str(e[0])
		e1 = str(e[1])
		if e0 +"_"+e1 not in edge_id:
			edge_id[e0+"_"+e1] = index
			edge_id[e1+"_"+e0] = index
		index = index + 1

	print("edges", len(G.edges()), index)


def generate_topology(k):
	import matplotlib.pyplot as plt
	G,_,edge_switches,hosts = generate_fattree(k)
	nx.draw_networkx(G)
	plt.savefig('fattree%d.pdf' % k)
	import json
	with open('fattree%d.json' % k,'w') as f:
		json.dump({"links": [list(map(str,list(l))) for l in G.edges()]},f, indent=2)
	print("nodes ", len(G.nodes()))
	print("links ", len(G.edges()))
	print("edges", list(map(str, edge_switches)))
	print("host", list(map(str, hosts)))
	print(hosts)

	start_node = hosts[0]
	print("start node:", start_node)
	stack = []
	stack.append(start_node)
	paths = {}
	dfs_path(G, stack, hosts, paths)
	#print(paths)

	edge_id = {}
	generate_edge_id(edge_id, G)

	assert_rechiable_node = ""
	for h in paths:
		if h != start_node:
			assert_rechiable_node += "(node[%s].status & (" % (str(int(h)-len(hosts)))
			for path in paths[h]:
				assert_path = "("
				for i in range(0, len(path)-1):
					assert_path += "edge[%s].status &" % edge_id[str(path[i])+"_"+str(path[i+1])]

				assert_path = assert_path[:-2]

				assert_rechiable_node += assert_path + ") |"

			assert_rechiable_node = assert_rechiable_node[:-2]

			assert_rechiable_node += ")) +"

	assert_rechiable_node = assert_rechiable_node[:-2]

	#print(assert_rechiable_node)
	return assert_rechiable_node, G, hosts


def main():
	#topo = FattreeTopo(k=4)
	k = 4
	assert_rechiable_node, G, hosts = generate_topology(k)

	link_failure = 4

	with open("templete.pml", "r") as f:
		pml = f.read()
		pml = pml.replace("[$NODE_NUM]", str(len(hosts))) \
				 .replace("[$EDGE_NUM]", str(len(G.edges()))) \
				 .replace("[$LINK_FAILURE]", str(link_failure)) \
				 .replace("[$MIN_NODE]", str(2)) \
				 .replace("[$ASSERT1]", assert_rechiable_node) \
				 .replace("[$EDGE_CAN_FAIL_INIT]", "")

		fw = open("update_rollout_controller_fattree"+str(k)+".pml", "w")
		fw.write(pml)

	
if __name__ == '__main__':
	main()