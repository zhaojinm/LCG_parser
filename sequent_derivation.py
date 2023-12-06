import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
from bs4 import BeautifulSoup
# import seaborn as sns
import matplotlib.pyplot as plt
from collections import defaultdict
import random

'''
Main idea about bounded order:
The key idea is that for each entry fi,j that represents the matchings from Xi to Xj(inclusive),
we only care about it integral critira is satisfied for subgraph that contains nodes from root to
Xi and nodes from root to Xj only. Both braketing and adjoin is a function of m. Worst case is
adjoin that combined graph contains 4m nodes at most.

For T(CT), if A+ solid access to B- and A does not solid access to B' lambda parent then CT is satisfied
for A. So verify CT also can be done during braket and adjoin with complexity a function of m.

n^2 entry, each entry does 1 brackt and O(n) adjoin.  Overall O(n^3).
'''
POS = 1
NEG = 0
node_num = 0
class UnfoldNode():
    def __init__(self, prim, num, sign) -> None:
        self.prim = prim
        self.num = num
        self.sign = sign
        self.right_child = []
        self.left_child = []
        self.par = None
        self.depth = 0

    def set_depth(self,depth):
        self.depth = depth
        for c in self.left_child+self.right_child:
            c.set_depth(depth+1)

    def __repr__(self) -> str:
        return self.prim + str(self.num) + " "+ str(self.sign)

    def __str__(self) -> str:
        return self.prim + str(self.num) + " "+ str(self.sign)
    def inorder(self):
        result = []
        for c in self.left_child:
            result.extend(c.inorder())
        result.append(self)
        for c in self.right_child:
            result.extend(c.inorder())
        return result

class Graph():
    def __init__(self,vertices,lambdaPairs,negativeNodes, postiveLambda):
        self.graph = defaultdict(set)
        self.V = vertices
        self.dashgraph = defaultdict(set)
        self.negativeNodes = negativeNodes
        self.lambdaPairs = lambdaPairs
        self.postiveLambda = postiveLambda
        self.negativePar = defaultdict(int)
        self.CT = set()
        self.matching = set()
        for p in lambdaPairs:
            self.negativePar[p[1]] = p[0]

    def addEdge(self,u,v):
        self.graph[u].add(v)

    def addDash(self,u,v):
        self.dashgraph[u].add(v)

    def isCyclicUtil(self, v, visited, recStack):
        visited[v] = True
        recStack[v] = True
        for neighbour in self.graph[v]:
            if visited[neighbour] == False:
                if self.isCyclicUtil(neighbour, visited, recStack) == True:
                    return True
            elif recStack[neighbour] == True:
                return True
        recStack[v] = False
        return False

    # Returns true if graph is cyclic else false
    def isCyclic(self):
        visited = dict()
        recStack = dict()
        for v in self.V:
            visited[v] = False
            recStack[v] = False
        for node in self.V:
            if visited[node] == False:
                if self.isCyclicUtil(node,visited,recStack) == True:
                    return True
        return False

    def isAccess(self, u, v):
        if u==v:
            return True
        visited = dict()
        for n in self.V:
            visited[n] = False
        queue = [u]
        while queue!=[]:
            cur = queue.pop(0)
            for neighbor in self.graph[cur]:
                if neighbor==v:
                    return True
                if visited[neighbor]!=visited:
                    queue.append(neighbor)
        return False

    def __str__(self) -> str:
        return str(self.graph)+str(self.dashgraph)+str(self.CT)+str(self.lambdaPairs)\
            +str(self.negativeNodes)+str(self.negativePar)+str(self.postiveLambda)+str(self.matching)+"\n"

    def __repr__(self) -> str:
        return str(self.graph)+str(self.dashgraph)+str(self.CT)+str(self.lambdaPairs)\
            +str(self.negativeNodes)+str(self.negativePar)+str(self.postiveLambda)+str(self.matching)+"\n"

    def isSame(self,other,empty_premises=True):
        if self.V!=other.V:
            return False
        for u in self.V:
            if self.graph[u]!=other.graph[u]:
                return False
            if self.dashgraph[u]!=other.dashgraph[u]:
                return False
        if not empty_premises:
            return self.CT==other.CT
        return True

def get_main_connective(cat):
    num_left_para=0
    for i,ch in enumerate(cat):
        if ch == "(":
            num_left_para+=1
        elif ch == ")":
            num_left_para-=1
        elif (ch=="/" or ch=="\\") and num_left_para==0:
            B = cat[i+1:]
            if B.count("/") + B.count("\\") >0:
                B = B[1:-1]
            A = cat[:i]
            if A.count("/") + A.count("\\") >0:
                A = A[1:-1]
            # print(ch,i,B,A)
            return ch, i, B, A
    return "", -1, "", ""

'''
A/B-: A- -->  B+
A\B-: B+  <-- A-
A/B+: B-  <--(dash) A+
A\B+: A+ -->(dash) B+
'''
def get_unfolding(c, sign):
    if c.count("/")+c.count("\\")==0:
        global node_num
        node_num += 1
        return UnfoldNode(c, node_num, sign)
    ch,i,B,A = get_main_connective(c)
    if ch=="/" and sign==NEG:
        A_node = get_unfolding(A,NEG)
        B_node = get_unfolding(B,POS)
        A_node.right_child.append(B_node)
        B_node.par = A_node
        return A_node
    elif ch=="\\" and sign ==NEG:
        B_node = get_unfolding(B,POS)
        A_node = get_unfolding(A,NEG)
        A_node.left_child.insert(0,B_node)
        B_node.par = A_node
        return A_node
    elif ch=="/" and sign==POS:
        B_node = get_unfolding(B,NEG)
        A_node = get_unfolding(A,POS)
        A_node.left_child.insert(0,B_node)
        B_node.par = A_node
        return A_node
    elif ch=="\\" and sign==POS:
        A_node = get_unfolding(A,POS)
        B_node = get_unfolding(B,NEG)
        A_node.right_child.append(B_node)
        B_node.par = A_node
        return A_node

def get_result_node(unfolding_formulae:list, s:int, e:int)->set:
    result = set()
    start_node = unfolding_formulae[s-1]
    end_node = unfolding_formulae[e-1]
    result_negativeNodes = set()
    result_lambda_pairs = set()
    start_path = []
    end_path = []
    result_lambda_nodes = set()

    if start_node.sign==POS and start_node.par!=None and \
        (start_node.left_child!=[] or start_node.right_child!=[]):
        result_lambda_nodes.add(start_node.num)
    if end_node.sign==POS and end_node.par!=None and \
        (end_node.left_child!=[] or end_node.right_child!=[]):
        result_lambda_nodes.add(end_node.num)

    while start_node:
        result.add(start_node.num)
        start_path.insert(0,start_node.num)
        start_node = start_node.par

    while end_node:
        result.add(end_node.num)
        end_path.insert(0,end_node.num)
        end_node = end_node.par

    for i,c in enumerate(start_path):
        if i%2==0 and i!=len(start_path)-1 and i!=0:
            result_lambda_nodes.add(c)
        if i%2==1:
            result_negativeNodes.add(c)
        if i%2==1 and i>=3:
            result_lambda_pairs.add((start_path[i-1], c))
    for i,c in enumerate(end_path):
        if i%2==0 and i!=len(end_path)-1 and i!=0:
            result_lambda_nodes.add(c)
        if i%2==1:
            result_negativeNodes.add(c)
        if i%2==1 and i>=3:
            result_lambda_pairs.add((end_path[i-1], c))

    return result, start_path, end_path, result_lambda_nodes, result_negativeNodes, result_lambda_pairs

def combine(graph1, graph2, result_nodes,result_negativeNodes, result_lambda_pairs,\
    result_lambda_nodes,get_matching=False):
    combine_graph =Graph(graph1.V.union(graph2.V),graph1.lambdaPairs.union(graph2.lambdaPairs),\
        graph1.negativeNodes.union(graph2.negativeNodes),graph1.postiveLambda.union(graph2.postiveLambda))
    combine_graph.CT = graph1.CT.union(graph2.CT)
    if get_matching:
        for m1 in graph1.matching:
            if len(graph2.matching)>0:
                for m2 in graph2.matching:
                    combine_graph.matching.add(m1+m2)
            else:
                combine_graph.matching.add(m1)
    #combine
    for u in graph1.graph:
        for v in graph1.graph[u]:
            combine_graph.addEdge(u,v)
    for u in graph2.graph:
        for v in graph2.graph[u]:
            combine_graph.addEdge(u,v)
    for u in graph1.dashgraph:
        for v in graph1.dashgraph[u]:
            combine_graph.addDash(u,v)
    for u in graph2.dashgraph:
        for v in graph2.dashgraph[u]:
            combine_graph.addDash(u,v)

    #check cycle
    if combine_graph.isCyclic():
        return None

    result_graph = Graph(result_nodes,result_lambda_pairs,result_negativeNodes,result_lambda_nodes)
    result_graph.matching = combine_graph.matching

    for u in result_nodes:
        for v in result_nodes:
            if u!=v:
                isAcess = combine_graph.isAccess(u,v)
                if isAcess:
                    result_graph.addEdge(u,v)
    # print(result_graph)
    # print(combine_graph.CT)
    for u in combine_graph.dashgraph:
        for v in combine_graph.dashgraph[u]:
            if u in result_nodes and v in result_nodes:
                if combine_graph.isAccess(u,v):
                    result_graph.addEdge(u,v)
                else:
                    result_graph.addDash(u,v)
            elif u not in result_nodes and v not in result_nodes:
                if combine_graph.isAccess(u,v):
                    pass
                else:
                    return None
            elif u in result_nodes and v not in result_nodes:
                if combine_graph.isAccess(u,v):
                    pass
                else:
                    flag = False
                    for n in result_nodes:
                        if combine_graph.isAccess(n,v):
                            flag=True
                            result_graph.addDash(u,n)
                            break
                    if not flag:
                        return None
            #special case: consider later
            elif u not in result_nodes and v in result_nodes:
                if combine_graph.isAccess(u,v):
                    pass
                else:
                    return None
    if not empty_premises:
        for u in combine_graph.postiveLambda:
            if u not in combine_graph.CT:
                for v in combine_graph.negativeNodes:
                    if combine_graph.isAccess(u,v) and (not combine_graph.isAccess(u,combine_graph.negativePar[v])):
                        combine_graph.CT.add(u)
                        break
        result_graph.CT = result_nodes.intersection(combine_graph.CT)
        for u in combine_graph.postiveLambda:
            if u not in result_nodes and u not in combine_graph.CT:
                return None
    return result_graph

def add_entry(cur_entry, new_graph,empty_premiese=False, get_matching=False):
    for g in cur_entry:
        if g.isSame(new_graph,empty_premiese):
            if get_matching:
                for m in new_graph.matching:
                    g.matching.add(m)
            return
    cur_entry.add(new_graph)

def parse_sequent(cat_list, empty_premises,get_matching):
    global node_num
    node_num = 0
    terms = []
    for c in cat_list[:-1]:
        term = get_unfolding(c,NEG)
        terms.append(term)
    rhs = get_unfolding(cat_list[-1],POS)
    for term in terms:
        rhs.left_child.append(term)
        term.par = rhs
    unfolding_formulae = rhs.inorder()
    rhs.set_depth(0)
    # print(unfolding_formulae)
    f = []


    # assert [i+1 for i in range(len(unfolding_formulae))] == [e.num for e in unfolding_formulae]
    for l in range(2, len(unfolding_formulae)+1, 2):
        cur_f = []
        for s in range(1, len(unfolding_formulae)-l+2):
            e = s + l - 1
            cur_entry = set()
            result_nodes,start_path,end_path, result_lambda_nodes, result_negativeNodes, result_lambda_pairs \
                = get_result_node(unfolding_formulae, s, e)
            # print(s, e, result_nodes, start_path, end_path,result_lambda_nodes)
            #brackeing //todo
            if unfolding_formulae[s-1].prim == unfolding_formulae[e-1].prim and unfolding_formulae[s-1].sign + unfolding_formulae[e-1].sign==1:
                if unfolding_formulae[s-1].sign==POS:
                    pos_node = unfolding_formulae[s-1]
                    neg_node = unfolding_formulae[e-1]
                else:
                    neg_node = unfolding_formulae[s-1]
                    pos_node = unfolding_formulae[e-1]
                outer_graph = Graph(result_nodes,result_lambda_pairs,result_negativeNodes,result_lambda_nodes)
                outer_graph.matching.add("("+str(s)+" "+str(e)+")")
                for i,n in enumerate(start_path[:-1]):
                    if i%2==0:
                        outer_graph.addDash(n,start_path[i+1])
                    else:
                        outer_graph.addEdge(n,start_path[i+1])
                for i,n in enumerate(end_path[:-1]):
                    if i%2==0:
                        outer_graph.addDash(n,end_path[i+1])
                    else:
                        outer_graph.addEdge(n,end_path[i+1])
                outer_graph.addEdge(pos_node.num,neg_node.num)
                if not outer_graph.isCyclic():
                    if l==2:
                        cur_entry.add(combine(outer_graph,Graph(set(),set(),set(),set()),result_nodes,result_negativeNodes, result_lambda_pairs,result_lambda_nodes,get_matching))
                    elif inner_entry := f[(l-2)//2-1][s]:
                        # print("bracketing")
                        for inner_graph in inner_entry:
                            new_graph = combine(outer_graph, inner_graph,result_nodes,result_negativeNodes, result_lambda_pairs,result_lambda_nodes,get_matching)
                            if new_graph:
                                add_entry(cur_entry, new_graph,empty_premises,get_matching)
            #adjoin
            for k in range(s+1,e-1,2):
                left_entry = f[(k-s+1)//2-1][s-1]
                right_entry = f[(e-k)//2-1][k]

                if left_entry and right_entry:
                    # print("adjoin",k)
                    for graph1 in left_entry:
                        for graph2 in right_entry:
                            new_graph = combine(graph1, graph2, result_nodes,result_negativeNodes, result_lambda_pairs,result_lambda_nodes,get_matching)
                            if new_graph:
                                add_entry(cur_entry, new_graph,empty_premises,get_matching)
            if len(cur_entry)>0:
                cur_f.append(cur_entry)
            else:
                cur_f.append(None)
        # print(cur_f)
        # print()
        f.append(cur_f)

    return f
    # return unfolding_formulae

def parse_txt(folder="trn", empty_premises = False, get_matching=False):
    count = 0
    with open('./LCbank.'+folder+'.str') as f:
        for line in f.readlines():
            # print(line,end="")
            l = line.split()
            rhs = l[-1]
            f = parse_sequent(l[:-2] + [rhs], empty_premises, get_matching)
            final_graphs =  f[-1][-1]
            answer = False
            if final_graphs:
                for g in final_graphs:
                    if sum([len(g.dashgraph[v]) for v in g.V])==0:
                        if not empty_premises and g.postiveLambda-g.CT==set():
                            if get_matching:
                                print(g.matching)
                            answer = True
                            # break
                        elif empty_premises:
                            if get_matching:
                                print(g.matching)
                            answer=True
                            break
            if answer:
                print("Sequent " + str(count) + " is derivable")
            else:
                print("Sequent " + str(count) + " is not derivable")
            count+=1

def parse_xml(folder="trn", empty_premises = False, get_matching=False):
    with open('./data/LCGbank.'+folder+'.xml') as f:
        data = f.read()
    _data = BeautifulSoup(data,"xml")
    right_ = _data.find_all("sentential")
    words = _data.find_all("words")
    matching = _data.find_all("matching")
    sentence = _data.find_all("sentence")

    curpus_level_prob = 0
    seen_sen = 0
    total_yield = 0
    last_idx = 1000000
    num = 0
    for ws,mt,r,s in zip(words[:last_idx],matching[:last_idx],right_[:last_idx],sentence[:last_idx]):
        cur_cat = []
        cur_match = {}
        cur_cat_with_num = []
        cur_match_str = ""
        for w in ws.find_all("word"):
            try:
                c = "".join([l for l in w["cat"] if l.isalpha() or l in "/\\()"])
                cur_cat.append(c)
                cur_cat_with_num.append("".join([l for l in w["cat"]]))
            except:
                pass
        for m in mt.find_all("match"):
            cur_match_str +="("+str(min(int(m["negative"]),int(m["positive"])))+" "\
                +str(max(int(m["negative"]),int(m["positive"])))+")"
            cur_match[int(m["negative"])] = int(m["positive"])
            cur_match[int(m["positive"])] = int(m["negative"])
        # cur_cat.append("".join([l for l in r["cat"] if l.isalpha() or l in "/\\()"]))
        rhs = r['cat']
        inside_cat = False
        # for key in cur_match:
        #     for cat in cur_cat_with_num:
        #         if "_"+str(key) in cat and "_"+str(cur_match[key]) in cat:
        #             inside_cat=True
        #             print(key,cur_match[key])
        #             break
        if rhs.count("/")+rhs.count("\\")==0 and not inside_cat:
            # cur_str = " ".join(cur_cat_with_num)+" -> "+rhs
            # cur_str = "".join([i for i in cur_str if not i.isdigit() and i!="_"])
            # print(cur_str)
            print(s['id'])
            # # print(cur_match_str)
            f = parse_sequent(cur_cat_with_num + [rhs], empty_premises, get_matching)
            for key in cur_match:
                if abs(f[key-1].depth - f[cur_match[key]-1].depth)!=1:
                    print(f[key-1].depth - f[cur_match[key]-1].depth)
                    print(s['id'],r['cat'])
                    # exit()
            # final_graphs =  f[-1][-1]
            # answer = False
            # same_match = False
            # if final_graphs:
            #     for g in final_graphs:
            #         if sum([len(g.dashgraph[v]) for v in g.V])==0:
            #             if not empty_premises and g.postiveLambda-g.CT==set():
            #                 if get_matching:
            #                     print(g.matching)
            #                     for m_s in g.matching:
            #                         if m_s == cur_match_str:
            #                             same_match = True
            #                 answer = True
            #                 # break
            #             elif empty_premises:
            #                 if get_matching:
            #                     print(g.matching)
            #                     for m_s in g.matching:
            #                         if m_s == cur_match_str:
            #                             same_match = True
            #                 answer=True
            #                 break
            # print("derivable:" + str(answer), " same match:"+ str(same_match)+ rhs)
        # else:
            # while rhs.count("/")+rhs.count("\\")!=0:
            #     ch,i,B,A = get_main_connective(rhs)
            #     # print(A,B)
            #     if ch =="/":
            #         cur_cat_with_num.append(B)
            #     else:
            #         cur_cat_with_num.insert(0,B)
            #     rhs = A
            # cur_str = " ".join(cur_cat_with_num)+" -> "+rhs
            # cur_str = "".join([i for i in cur_str if not i.isdigit() and i!="_"])
            # print(cur_str)

def generate_random_sequent(num= 10000):
    count = 0
    all_cat = []
    with open('./LCbank.trn.str') as f:
        for line in f.readlines():
            l = line.split()
            all_cat.extend(l[:-2])
    print(len(set(all_cat)))
    while count<num:
        cur_sequent = []
        length = random.randint(3,50)
        for cat_i in range(length):
            idx = random.randint(0,len(all_cat)-1)
            cur_sequent.append(all_cat[idx])
        global node_num
        node_num = 0
        rhs = get_unfolding("S", POS)
        for c in cur_sequent:
            term = get_unfolding(c,NEG)
            rhs.left_child.append(term)
            term.par = rhs
        unfolding_formulae = rhs.inorder()
        signs = [i.sign for i in unfolding_formulae]
        prims = [i.prim for i in unfolding_formulae]
        # print(signs)
        # print(prims)
        flag = True
        if signs.count(POS) != signs.count(NEG):
            flag = False
        for p in set(prims):
            if prims.count(p)%2!=0:
                flag = False
                break
        if flag:
            # print(signs)
            # print(prims)
            print(" ".join(cur_sequent[:])+" -> S")
            count+=1


if __name__ == "__main__":
    folder = "tst"
    # folder = "random.1k.order8.breadth3"
    #set False for L calculas
    empty_premises = True
    get_matching = False
    parse_txt(folder, empty_premises, get_matching)
    # generate_random_sequent(10000)
    # g = Graph(set([1,3,5,7]))
    # g.addEdge(1,3)
    # g.addEdge(1,5)
    # g.addEdge(3,5)
    # g.addEdge(5,7)
    # print(g.isCyclic())
    # print(g.isAccess(3,7))
    # print(g.isAccess(7,3))
    # print(g)
