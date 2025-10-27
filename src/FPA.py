import networkx as nx
import sys, math
from collections import defaultdict
from collections import deque
import time
import argparse
import heapq
import os


sys.setrecursionlimit(10 ** 6)



class Node:
    __slots__ = ['id', 'left', 'right', 'parent', 'rev']

    def __init__(self, id):
        self.id = id
        self.left = None
        self.right = None
        self.parent = None
        self.rev = False

def is_root(x):
    return (x.parent is None) or (x.parent.left != x and x.parent.right != x)


def push(x):
    if x and x.rev:
        x.left, x.right = x.right, x.left
        if x.left:
            x.left.rev ^= True
        if x.right:
            x.right.rev ^= True
        x.rev = False


def update(x):
    pass


def rotate(x):
    p = x.parent
    g = p.parent
    push(p)
    push(x)
    if p.left == x:
        p.left = x.right
        if x.right:
            x.right.parent = p
        x.right = p
    else:
        p.right = x.left
        if x.left:
            x.left.parent = p
        x.left = p
    p.parent = x
    x.parent = g
    if g:
        if g.left == p:
            g.left = x
        elif g.right == p:
            g.right = x
    update(p)
    update(x)


def splay(x):
    while not is_root(x):
        p = x.parent
        g = p.parent
        if not is_root(p):
            if (g.left == p) == (p.left == x):
                rotate(p)  # zig-zig
            else:
                rotate(x)  # zig-zag
        rotate(x)
    push(x)
    update(x)


def access(x):
    last = None
    y = x
    while y:
        splay(y)
        y.right = last
        update(y)
        last = y
        y = y.parent
    splay(x)
    return last


def make_root(x):
    access(x)
    x.rev ^= True
    push(x)


def find_root(x):
    access(x)
    while x.left:
        push(x)
        x = x.left
    splay(x)
    return x


def connected_lct(x, y):
    return find_root(x) == find_root(y)


def link_lct(x, y):
    make_root(x)
    if find_root(y) != x:
        x.parent = y


def cut_lct(x, y):
    make_root(x)
    access(y)
    if y.left == x:
        y.left.parent = None
        y.left = None
    update(y)


class LinkCutTree:
    def __init__(self, n):
        self.n = n
        self.nodes = [Node(i) for i in range(n)]

    def connected(self, u, v):
        return connected_lct(self.nodes[u], self.nodes[v])

    def link(self, u, v):
        if not self.connected(u, v):
            link_lct(self.nodes[u], self.nodes[v])

    def cut(self, u, v):
        # 양 방향 모두 시도 (어느 쪽이 부모인지 모를 수 있으므로)
        make_root(self.nodes[u])
        access(self.nodes[v])
        if self.nodes[v].left == self.nodes[u]:
            self.nodes[v].left.parent = None
            self.nodes[v].left = None
            update(self.nodes[v])
        else:
            make_root(self.nodes[v])
            access(self.nodes[u])
            if self.nodes[u].left == self.nodes[v]:
                self.nodes[u].left.parent = None
                self.nodes[u].left = None
                update(self.nodes[u])



class FullyDynamicConnectivity:
    def __init__(self, n):
        self.n = n
        self.comp_count = n
        self.L = math.ceil(math.log2(n)) if n > 1 else 1  # 최대 레벨
        self.forests = [LinkCutTree(n) for _ in range(self.L + 1)]
        self.non_tree_edges = [set() for _ in range(self.L + 1)]
        self.edge_level = {}
        self.is_tree_edge = {}

    def insert_edge(self, u, v):
        if u > v:
            u, v = v, u
        if (u, v) in self.edge_level:
            return
        level = 0
        self.edge_level[(u, v)] = 0
        if not self.forests[0].connected(u, v):
            for i in range(0, self.L + 1):
                self.forests[i].link(u, v)
            self.is_tree_edge[(u, v)] = True
            self.comp_count -= 1  # 두 컴포넌트가 합쳐짐
        else:
            self.non_tree_edges[0].add((u, v))
            self.is_tree_edge[(u, v)] = False

    def delete_edge(self, u, v):
        if u > v:
            u, v = v, u
        if (u, v) not in self.edge_level:
            return
        level = self.edge_level[(u, v)]
        del self.edge_level[(u, v)]
        if not self.is_tree_edge[(u, v)]:
            self.non_tree_edges[level].discard((u, v))
            del self.is_tree_edge[(u, v)]
        else:
            for i in range(level, self.L + 1):
                if self.forests[i].connected(u, v):
                    self.forests[i].cut(u, v)
            del self.is_tree_edge[(u, v)]
            replacement = None
            rep_level = None
            for l in range(level, -1, -1):
                for e in list(self.non_tree_edges[l]):
                    x, y = e
                    if not self.forests[l].connected(x, y):
                        replacement = e
                        rep_level = l
                        break
                if replacement is not None:
                    break
            if replacement is not None:
                self.non_tree_edges[rep_level].remove(replacement)
                self.is_tree_edge[replacement] = True
                for i in range(rep_level, self.L + 1):
                    if not self.forests[i].connected(replacement[0], replacement[1]):
                        self.forests[i].link(replacement[0], replacement[1])
            else:
                self.comp_count += 1
            for l in range(level + 1):
                to_promote = []
                for e in list(self.non_tree_edges[l]):
                    x, y = e
                    if self.forests[l].connected(x, y):
                        to_promote.append(e)
                for e in to_promote:
                    self.non_tree_edges[l].remove(e)
                    new_level = l + 1
                    if new_level <= self.L:
                        self.non_tree_edges[new_level].add(e)
                        self.edge_level[e] = new_level
                    else:
                        if e in self.edge_level:
                            del self.edge_level[e]

    def connected(self, u, v):
        return self.forests[0].connected(u, v)

    def get_component_count(self):
        return self.comp_count


def load_network(file_path):
    G = nx.Graph()
    with open(file_path, 'r') as f:
        for line in f:
            if line.startswith('#'):
                continue
            u, v = map(int, line.strip().split())
            G.add_edge(u, v)

    mapping = {}
    for new_label, old_label in enumerate(G.nodes()):
        mapping[old_label] = new_label

    G = nx.relabel_nodes(G, mapping)
    return G

def is_flexiclique(S, G, tau):
    if not S:
        return False
    k = len(S)
    if k == 1:
        return True
    threshold = math.floor(k ** tau)
    subgraph = G.subgraph(S)
    min_deg = min(dict(subgraph.degree()).values())
    return min_deg >= threshold



def k_core_seed(G, tau):
    cores = nx.core_number(G)
    k_star = max(cores.values())

    # 시작 k 값과 초기 값
    k = 2
    best_k = k
    T = None

    while k <= k_star:
        # 코어 넘버가 k 이상인 노드 추출
        nodes_k = [node for node, core in cores.items() if core >= k]

        if not nodes_k:
            break

        sub_g = G.subgraph(nodes_k)
        components = list(nx.connected_components(sub_g))

        if not components:
            break

        largest_cc = max(components, key=lambda comp: len(comp))
        T = sub_g.subgraph(largest_cc)

        # Flexi-clique 조건 검사
        if math.floor(T.number_of_nodes() ** tau) <= k:
            best_k = k
            print("size of feasible k-core:", k, "-core", T.number_of_nodes())
            break

        k += 1

    k -= 1
    # best_k - 1 코어에서 T를 포함하는 connected component를 찾기
    nodes_km1 = [node for node, core in cores.items() if core >= best_k - 1]

    if not nodes_km1:
        return None  # 더 이상 유효한 노드가 없는 경우

    sub_g_km1 = G.subgraph(nodes_km1)

    if k != k_star:
        # T의 노드 중 하나가 포함된 connected component만 선택
        for component in nx.connected_components(sub_g_km1):
            if set(T.nodes()).intersection(component):
                final_component = sub_g_km1.subgraph(component)
                return final_component, T, cores,k
    else:
        return [], [],cores,k  # k_star인 경우, 모든 노드가 포함된 컴포넌트 반환


def largest_feasible_connected_component(G, tau):
    cores = nx.core_number(G)
    k_star = max(cores.values())

    # 시작 k 값과 초기 값
    k = 2
    best_k = k
    T = None

    while k <= k_star:
        # 코어 넘버가 k 이상인 노드 추출
        nodes_k = [node for node, core in cores.items() if core >= k]

        if not nodes_k:
            break

        sub_g = G.subgraph(nodes_k)
        components = list(nx.connected_components(sub_g))

        if not components:
            break

        largest_cc = max(components, key=lambda comp: len(comp))
        T = sub_g.subgraph(largest_cc)

        # Flexi-clique 조건 검사
        if math.floor(T.number_of_nodes() ** tau) <= k:
            best_k = k
            print("size of feasible k-core:" , k,"-core",  T.number_of_nodes())
            break

        k += 1

    k -= 1
    # best_k - 1 코어에서 T를 포함하는 connected component를 찾기
    nodes_km1 = [node for node, core in cores.items() if core >= best_k-1]

    if not nodes_km1:
        return None  # 더 이상 유효한 노드가 없는 경우

    sub_g_km1 = G.subgraph(nodes_km1)

    if k != k_star:
        # T의 노드 중 하나가 포함된 connected component만 선택
        for component in nx.connected_components(sub_g_km1):
            if set(T.nodes()).intersection(component):
                final_component = sub_g_km1.subgraph(component)
                return final_component, T
    else:
        return G.subgraph(T), T  # k_star인 경우, 모든 노드가 포함된 컴포넌트 반환






def flexi_clique(G, T, tau):
    n = G.number_of_nodes()
    G.subgraph(T)  # Ensure T is a subgraph of G
    print("G", G)
    fdc = FullyDynamicConnectivity(n)

    for (u, v) in G.edges:
        fdc.insert_edge(u, v)

    # min degree of T
    min_deg = min(dict(T.degree()).values())

    if min_deg >= math.floor(len(T) ** tau):
        best_component_size = len(T)
        best_component = T
    else:
        best_component_size = 0
        best_component = None

    C = set(G.nodes())

    # 초기 adjacency와 degree 계산
    comp_adj = {node: set(G.neighbors(node)) for node in C}
    node_deg = {node: len(neighbors) for node, neighbors in comp_adj.items()}

    # Bucket sort: degree별로 노드들을 분류
    max_degree = max(node_deg.values()) if node_deg else 0
    buckets = [[] for _ in range(max_degree + 1)]

    for node in C:
        degree = node_deg[node]
        buckets[degree].append(node)

    current_degree = min(node_deg[node] for node in C)
    checked_nodes_in_current_bucket = set()  # 현재 bucket에서 이미 확인한 노드들

    while len(C) > best_component_size:
        # 1. 먼저 현재 그래프가 flexi 조건을 만족하는지 확인
        min_deg = min(node_deg[node] for node in C) if C else 0
        threshold = math.floor(len(C) ** tau)
        if min_deg >= threshold:
            print(f"Found flexi-clique with size {len(C)}")
            if len(C) > best_component_size:
                best_component_size = len(C)
                best_component = set(C)
            break

        # 2. 현재 degree bucket이 비어있거나 모든 노드를 확인했으면 다음 degree로 이동
        while (current_degree <= max_degree and
               (not buckets[current_degree] or
                all(node in checked_nodes_in_current_bucket or node not in C
                    for node in buckets[current_degree]))):
            current_degree += 1
            checked_nodes_in_current_bucket.clear()  # 새로운 bucket에서는 확인 리스트 리셋

        # 3. 더 이상 확인할 degree가 없으면 종료
        if current_degree > max_degree:
            break

        # 4. 현재 bucket에서 아직 확인하지 않은 노드 선택
        candidate = None
        for node in buckets[current_degree]:
            if node in C and node not in checked_nodes_in_current_bucket:
                candidate = node
                break

        if candidate is None:
            current_degree += 1
            checked_nodes_in_current_bucket.clear()
            continue

        # 5. 현재 노드의 degree가 변경되었는지 확인
        if node_deg[candidate] != current_degree:
            # degree가 변경되었으면 올바른 bucket으로 이동
            buckets[current_degree].remove(candidate)
            new_deg = node_deg[candidate]
            if new_deg <= max_degree:
                buckets[new_deg].append(candidate)
            continue

        # 6. 현재 노드를 확인했다고 표시
        checked_nodes_in_current_bucket.add(candidate)

        # 7. articulation node 체크를 위한 edge 삭제
        candidate_edges = [(candidate, neighbor) for neighbor in comp_adj[candidate]]
        old_nc = fdc.get_component_count()

        for (u, v) in candidate_edges:
            u0, v0 = u, v
            key = (min(u0, v0), max(u0, v0))
            if key in fdc.edge_level:
                fdc.delete_edge(u0, v0)

        new_nc = fdc.get_component_count()
        diff = new_nc - old_nc

        start_time = time.time()

        if diff == 1:  # articulation node가 아님 -> 삭제 가능
            print(f"Candidate {candidate} accepted; deleting candidate. remaining nodes: {len(C)}")

            # 그래프에서 노드 제거
            G.remove_node(candidate)
            C.remove(candidate)

            # 이웃 노드들의 degree를 1씩 감소시키고 bucket 이동
            neighbors_to_update = list(comp_adj[candidate])

            for neighbor in neighbors_to_update:
                if neighbor in comp_adj:
                    # 이웃의 adjacency에서 candidate 제거
                    comp_adj[neighbor].remove(candidate)
                    old_deg = node_deg[neighbor]
                    new_deg = old_deg - 1
                    node_deg[neighbor] = new_deg

                    # bucket에서 이웃 노드를 찾아서 이동
                    if neighbor in buckets[old_deg]:
                        buckets[old_deg].remove(neighbor)
                        if new_deg >= 0:
                            buckets[new_deg].append(neighbor)

            # candidate 자체를 bucket에서 제거
            if candidate in buckets[current_degree]:
                buckets[current_degree].remove(candidate)

            # candidate 자체의 정보 삭제
            if candidate in comp_adj:
                del comp_adj[candidate]
            if candidate in node_deg:
                del node_deg[candidate]

            # 노드가 삭제되었으므로 확인 리스트에서도 제거
            checked_nodes_in_current_bucket.discard(candidate)
            current_degree = min(node_deg[node] for node in C)

        else:  # articulation node임 -> 삭제 불가, edge 복원
            for (u, v) in candidate_edges:
                fdc.insert_edge(u, v)
            # articulation node는 bucket에서 제거하지 않음! 다음 iteration에서 다시 고려

        print(f"processing time: {time.time() - start_time}")

    return best_component

def modified_greedy_plus_plus(G, tau):

    candidates = []
    best_flexi = set()
    global_best_size = 0

    comp_heap = [(-len(comp), comp) for comp in nx.connected_components(G)]
    heapq.heapify(comp_heap)

    while comp_heap:
        _, comp = heapq.heappop(comp_heap)
        comp = set(comp)

        min_deg_comp = min(G.degree[node] for node in comp)
        candidate_max_size = math.floor(min_deg_comp ** (1 / tau))
        if candidate_max_size <= global_best_size:
            continue

        subgraph = G.subgraph(comp).copy()
        loads = {node: 0 for node in subgraph.nodes}
        heap = [(loads[node] + degree, node) for node, degree in subgraph.degree]
        heapq.heapify(heap)
        remaining_nodes = set(subgraph.nodes)
        current_degrees = dict(subgraph.degree)

        while remaining_nodes:
            num_nodes = len(remaining_nodes)
            threshold = math.floor(num_nodes ** tau)

            while heap:
                score, node = heapq.heappop(heap)
                if node in remaining_nodes and (loads[node] + current_degrees[node] == score):
                    min_degree = current_degrees[node]
                    break
            # else:
            #     break


            if min_degree >= threshold:
                candidate_set = set(remaining_nodes)
                comps = list(nx.connected_components(G.subgraph(candidate_set)))
                if len(comps) == 1:
                    min_degree_original = min(G.degree[node] for node in candidate_set)
                    if len(candidate_set) > global_best_size:
                        global_best_size = len(candidate_set)
                        best_flexi = candidate_set
                    candidates.append((candidate_set, min_degree_original))
                else:
                    for new_comp in comps:
                        heapq.heappush(comp_heap, (-len(new_comp), new_comp))
                break

            remaining_nodes.remove(node)
            loads[node] += current_degrees[node]
            visited = set()

            for neighbor in list(subgraph.neighbors(node)):
                if neighbor in remaining_nodes and neighbor not in visited:
                    current_degrees[neighbor] -= 1
                    heapq.heappush(heap, (loads[neighbor] + current_degrees[neighbor], neighbor))
                    visited.add(neighbor)

    return best_flexi, global_best_size




def expand_candidates(G, candidates, tau):
    expanded_subgraphs = []

    sorted_candidates = sorted(candidates, key=lambda x: len(x[0]), reverse=True)

    for candidate_set, _ in sorted_candidates:
        expanded_set = set(candidate_set)
        neighbors_to_explore = set(neigh for node in candidate_set for neigh in G.neighbors(node)) - expanded_set


        while neighbors_to_explore:
            neighbors_to_explore = set(sorted(neighbors_to_explore, key=lambda node: G.degree[node], reverse=True))

            new_node = neighbors_to_explore.pop()
            expanded_set.add(new_node)

            subgraph = G.subgraph(expanded_set)
            min_degree = min(subgraph.degree[node] for node in expanded_set)
            threshold = math.floor(len(expanded_set) ** tau)

            if min_degree < threshold:
                expanded_set.remove(new_node)
                break

            neighbors_to_explore.update(set(G.neighbors(new_node)) - expanded_set)

        min_degree_original = min(G.degree[node] for node in expanded_set)
        expanded_subgraphs.append((expanded_set, min_degree_original))

    return expanded_subgraphs

