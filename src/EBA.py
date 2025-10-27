import networkx as nx
import math
import time
import sys
from collections import deque
import argparse
import os
from FPA import k_core_seed
from FPA import flexi_clique
from bottom_up import modified_greedy_plus_plus

sys.setrecursionlimit(10000)

# Global variables
best_flexiclique = set()
best_size = 0
discarded = set()  # 전역적으로 제거(pruning)된 노드들
node_info = {}  # { node: { 'degree': int, 'neighbors': set(...) } }
initial_order = []  # 초기 정렬 순서 (degree 오름차순, node_info 기준)
theta = 0  # pruning threshold
branch_num = 0


class MultiSourceShortestPath:
    def __init__(self, graph=None):
        self.graph = graph.copy() if graph else None
        self.sources = {}
        self.max_distances = {}

    def add_source(self, graph, new_source):
        """Add a new source and update max distances"""
        # 현재 graph로 업데이트 (중요!)
        self.graph = graph.copy()

        if new_source not in self.graph:
            print(f"Warning: {new_source} not in graph")
            return

        try:
            distances = nx.single_source_shortest_path_length(self.graph, new_source)
            self.sources[new_source] = distances

            for target, dist in distances.items():
                if target not in self.max_distances:
                    self.max_distances[target] = dist
                else:
                    # MAX distance 유지
                    self.max_distances[target] = max(self.max_distances[target], dist)

        except Exception as e:
            print(f"Error computing SSSP for {new_source}: {e}")
            self.sources[new_source] = {new_source: 0}
            if new_source not in self.max_distances:
                self.max_distances[new_source] = 0

    def delete_nodes(self, nodes_to_delete):
        if not nodes_to_delete:
            return

        nodes_to_delete = set(nodes_to_delete)

        if self.graph:
            existing_nodes = set(self.graph.nodes()) & nodes_to_delete
            if existing_nodes:
                self.graph.remove_nodes_from(existing_nodes)

        for source in list(self.sources.keys()):
            if source in nodes_to_delete:
                del self.sources[source]
            else:
                for node in nodes_to_delete:
                    if node in self.sources[source]:
                        del self.sources[source][node]

        for node in nodes_to_delete:
            if node in self.max_distances:
                del self.max_distances[node]

    def get_max_distance_from_S(self, target):
        """
        Get max distance from any source in S to target.
        Returns float('inf') if unreachable or no sources.
        """
        if not self.sources:
            return float('inf')

        if target not in self.max_distances:
            return float('inf')

        return self.max_distances[target]

    def get_all_max_distances(self):
        return self.max_distances.copy()

    def copy(self):
        new_msp = MultiSourceShortestPath()
        new_msp.graph = self.graph.copy() if self.graph else None
        new_msp.sources = {s: d.copy() for s, d in self.sources.items()}
        new_msp.max_distances = self.max_distances.copy()
        return new_msp

    def get_sources(self):
        return list(self.sources.keys())

    def has_source(self, source):
        return source in self.sources

    def get_distance(self, source, target):
        if source not in self.sources:
            return float('inf')
        return self.sources[source].get(target, float('inf'))

def preprocess_graph(G):
    node_info = {}
    for v in G.nodes():
        node_info[v] = {
            'degree': G.degree(v),
            'neighbors': set(G.neighbors(v))
        }
    return node_info


def core_fillter(cores, tau, best_size):
    theta = math.ceil((best_size+1) ** tau - 1)
    print("Core pruning threshold:", theta)
    subgraph = [node for node, core in cores.items() if core >= math.ceil(theta)]
    return subgraph


def iterative_prune(info, best_size, tau):
    theta = math.ceil((best_size+1) ** tau - 1)
    print("Pruning threshold:", theta)

    removed_set = set()
    queue = [v for v in info if info[v]['degree'] < math.ceil(theta)]

    while queue:
        v = queue.pop()
        if v in removed_set:
            continue
        removed_set.add(v)

        for u in info[v]['neighbors']:
            if u in info:
                info[u]['neighbors'].discard(v)
                info[u]['degree'] = len(info[u]['neighbors'])
                if info[u]['degree'] < theta and u not in removed_set:
                    queue.append(u)

        del info[v]
    return info, removed_set


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


def check_pruning_in_S(S, node_info, theta, D):
    for u in S:
        if u not in node_info:
            return True, u
        lost = sum(1 for w in node_info[u]['neighbors'] if w in D)
        if node_info[u]['degree'] - lost < theta:
            return True, u
    return False, None

_distance_threshold_cache = {}
_distance_upperbound_cache = {}
def find_distance_threshold(theta, tau, degree_v):
    """🚀 OPTIMIZED: 캐싱 + 이진 탐색"""
    # 캐시 키
    cache_key = (theta, tau, degree_v)
    if cache_key in _distance_threshold_cache:
        return _distance_threshold_cache[cache_key]

    # 🚀 이진 탐색으로 최적화
    theta_ceil = math.ceil(theta)

    # 상한 추정 (충분히 큰 값)
    left, right = 0, 1000

    # 빠른 상한 찾기
    while True:
        f_d = theta_ceil + right + 1 + (right // 3) * (theta_ceil - 2)
        if math.floor(f_d ** tau) > degree_v:
            break
        right *= 2
        if right > 100000:  # 안전장치
            break

    # 이진 탐색
    result = right
    while left < right:
        mid = (left + right) // 2
        f_d = theta_ceil + mid + 1 + (mid // 3) * (theta_ceil - 2)

        if math.floor(f_d ** tau) > degree_v:
            result = mid
            right = mid
        else:
            left = mid + 1

    _distance_threshold_cache[cache_key] = result
    return result


def find_distance_upperbound(theta, tau, degree_v):
    """🚀 OPTIMIZED: 캐싱 + 이진 탐색"""
    # 캐시 키
    cache_key = (theta, tau, degree_v)
    if cache_key in _distance_upperbound_cache:
        return _distance_upperbound_cache[cache_key]

    # 🚀 이진 탐색으로 최적화
    theta_ceil = math.ceil(theta)

    # 상한 추정 (충분히 큰 값)
    left, right = 0, 1000

    # 빠른 상한 찾기
    while True:
        f_d = theta_ceil + right + 1 + (right // 3) * (theta_ceil - 2)
        if math.floor(f_d ** tau) > degree_v:
            break
        right *= 2
        if right > 100000:  # 안전장치
            break

    # 이진 탐색
    result = right
    while left < right:
        mid = (left + right) // 2
        f_d = theta_ceil + mid + 1 + (mid // 3) * (theta_ceil - 2)

        if math.floor(f_d ** tau) > degree_v:
            result = mid
            right = mid
        else:
            left = mid + 1

    _distance_upperbound_cache[cache_key] = result
    return result


def k_core_collapse(G, theta, v):
    removed = set()
    queue = deque()
    deg = dict(G.degree())
    for nbr in G.neighbors(v):
        deg[nbr] -= 1
        if deg[nbr] < math.ceil(theta):
            queue.append(nbr)

    while queue:
        u = queue.popleft()
        if u in removed:
            continue
        removed.add(u)
        for w in G.neighbors(u):
            if w not in removed:
                deg[w] -= 1
                if deg[w] < math.ceil(theta):
                    queue.append(w)

    return removed


def best_collapser(G, deg, k, R):
    original_deg = deg

    best_node = None
    best_followers = set()
    max_followers = -1

    candidates = [u for u in R if u in G and any(deg[w] < math.ceil(theta) for w in G.neighbors(u))]

    for u in candidates:
        sim_deg = original_deg.copy()
        removed = {u}
        queue = deque([u])

        while queue:
            v = queue.popleft()
            for w in G.neighbors(v):
                if w in removed:
                    continue
                sim_deg[w] -= 1
                if sim_deg[w] < k:
                    removed.add(w)
                    queue.append(w)

        followers = removed

        if len(followers) > max_followers:
            max_followers = len(followers)
            best_node = u
            best_followers = followers - {u}

    return best_node, best_followers


def compute_follower(G, v, theta):
    sim_deg = dict(G.degree())
    removed = {v}
    queue = deque([v])

    while queue:
        x = queue.popleft()
        for nbr in G.neighbors(x):
            if nbr in removed:
                continue
            sim_deg[nbr] -= 1
            if sim_deg[nbr] < math.ceil(theta):
                removed.add(nbr)
                queue.append(nbr)

    return removed - {v}


def cp_branch_BFS(G, tau):
    """Fixed Multi-Source Shortest Path를 사용한 최적화된 브랜치"""
    global best_flexiclique, best_size, discarded, node_info, initial_order, theta, branch_num
    V = list(G.nodes())
    queue = deque()

    # 🚀 Root에서는 빈 Multi-SSSP로 시작
    root_msp = MultiSourceShortestPath(G)

    initial_state = ([], [], V, set(), root_msp)
    queue.append(initial_state)

    while queue:
        branch_num += 1

        S, Cr, Cun, D, msp = queue.popleft()

        bound = len(S) + len(Cr) + len(Cun)
        if bound <= best_size:
            continue

        if set(S).intersection(discarded):
            continue

        if discarded:
            Cr = [v for v in Cr if v not in discarded]
            Cun = [v for v in Cun if v not in discarded]

        G_ = G.subgraph(S + Cr + Cun).copy()
        deg = dict(G_.degree())

        if S:
            min_adjusted_deg = float('inf')

            for v in S:
                if v in node_info:
                    adjusted_deg = sum(1 for w in node_info[v]['neighbors'] if w in Cr or w in Cun)
                    min_adjusted_deg = min(min_adjusted_deg, adjusted_deg)

            # Pruning 조건 1: possible maximum 체크
            possible_maximum = math.floor((min_adjusted_deg + 1) ** (1 / tau))
            if len(S) >= possible_maximum:
                return

            # Pruning 조건 2: adjusted degree가 theta보다 작으면 pruning
            if min_adjusted_deg < theta:
                return

        prev_node = None
        prev_D = D.copy()  # 🚀 이전 형제의 D (초기값은 부모의 D)
        follower = set()

        if len(S) == 0:
            R = initial_order
        else:
            R = Cr[:]
        if not R:
            continue


        sibling_count = 0

        while R:
            sibling_count += 1

            if set(S).intersection(prev_D):
                break

            # 🚀 이전 형제의 D + 현재 follower + prev_node
            new_D = prev_D.copy()
            new_D.update(follower)

            if prev_node is not None:
                new_D.add(prev_node)

            nodes = follower | {prev_node}

            # 그래프 업데이트
            for i in nodes:
                if i in G_:
                    for j in G_.neighbors(i):
                        deg[j] -= 1
                    del deg[i]
                    G_.remove_node(i)

            R = [u for u in R if u in G_]
            if not R:
                continue

            # 🚀 단순화된 노드 선택: 항상 Cr의 첫 번째 노드
            v = R[0]

            # 🚀 하지만 Follower는 계산 (다음 형제 브랜치를 위해)
            follower = compute_follower(G_, v, theta)

            R.remove(v)
            if v in new_D:
                continue

            new_S = S + [v]
            prev_node = v
            prev_D = new_D  # 🚀 다음 형제를 위해 현재 D 저장

            # best_size 갱신 체크
            if len(new_S) > best_size and is_flexiclique(new_S, G, tau):
                best_flexiclique = new_S.copy()
                best_size = len(new_S)
                if math.floor((best_size + 1) ** tau - 1) > theta:
                    node_info, removed_nodes = iterative_prune(node_info, best_size, tau)
                    discarded.update(set(G.nodes()) - set(node_info.keys()))
                    new_D.update(discarded)
                    prev_D = new_D

                if set(S).intersection(new_D):
                    break
                if set(new_S).intersection(new_D):
                    continue

            theta = math.ceil((best_size + 1) ** tau - 1)

            # 🚀 Cr 업데이트: degree 오름차순으로 정렬
            old_cr_filtered = [node for node in Cr if node not in new_S and node not in new_D]

            # v의 이웃 중 Cun에 있던 노드들
            new_neighbors_from_cun = [w for w in node_info[v]['neighbors']
                                      if w in Cun and w not in new_S and w not in new_D]

            # 모든 노드를 합쳐서 degree 오름차순으로 정렬
            new_Cr = old_cr_filtered + new_neighbors_from_cun
            new_Cr.sort(key=lambda x: deg.get(x, 0))

            # Cun 업데이트
            new_Cun = [node for node in Cun
                       if node not in new_S and node not in new_Cr and node not in new_D]


            if len(new_S) + len(new_Cr) + len(new_Cun) <= best_size:
                break

            ### 🚀 Multi-Source Shortest Path 업데이트
            current_msp = msp.copy()

            # 1. 삭제된 노드들 처리
            nodes_to_delete = [n for n in nodes if n is not None]
            if nodes_to_delete:
                current_msp.delete_nodes(nodes_to_delete)

            current_msp.add_source(G_, v)

            # 3. Rule 4&5 적용

            valid_nodes_in_S = [n for n in new_S if n in G_]
            if not valid_nodes_in_S:
                continue

            min_deg = min(G_.degree(n) for n in valid_nodes_in_S)
            d_th = find_distance_threshold(theta, tau, min_deg)
            d_up = find_distance_upperbound(theta, tau, len(new_S + new_Cr + new_Cun))
            d_star = min(d_th, d_up)

            candidates_to_check = set(new_Cr) | set(new_Cun)

            remove_candidates = set()
            for candidate in candidates_to_check:
                max_dist = current_msp.get_max_distance_from_S(candidate)

                if max_dist > d_star or max_dist == float('inf'):
                    remove_candidates.add(candidate)

            if remove_candidates:
                new_D = new_D.union(remove_candidates)
                new_Cr = [node for node in new_Cr if node not in remove_candidates]
                new_Cun = [node for node in new_Cun if node not in remove_candidates]


            if len(new_S) + len(new_Cr) + len(new_Cun) <= best_size:
                continue

            if S:
                min_adjusted_deg = float('inf')

                for v_check in S:
                    if v_check in node_info:
                        adjusted_deg = sum(1 for w in node_info[v_check]['neighbors'] if w in new_Cr or w in new_Cun)
                        min_adjusted_deg = min(min_adjusted_deg, adjusted_deg)

                possible_maximum = math.floor((min_adjusted_deg + 1) ** (1 / tau))
                if len(S) >= possible_maximum:
                    break

                if min_adjusted_deg < theta:
                    break

            queue.append((new_S, new_Cr, new_Cun, new_D, current_msp))
            print(new_S, new_Cr, new_Cun, new_D)


def find_max_flexiclique(G, tau):
    global best_flexiclique, best_size, discarded, node_info, initial_order, theta, branch_num
    best_flexiclique = set()

    cores = nx.core_number(G)
    print("max core number:", max(cores.values()))

    cand, size = modified_greedy_plus_plus(G, tau)
    subgraph = G.subgraph(cand)

    best_size = size -1
    initial_best_size = best_size
    print("Initial candidate size:", best_size)

    H = core_fillter(cores, tau, best_size)
    print("size of H:", len(H))

    if not H:
        return cand, best_size, initial_best_size, len(subgraph.edges()), branch_num

    H = G.subgraph(H)

    node_info = preprocess_graph(H)

    initial_order = sorted(list(node_info.keys()), key=lambda v: node_info[v]['degree'])
    cp_branch_BFS(H, tau)
    if not best_flexiclique:
        return cand, best_size, initial_best_size, len(subgraph.edges()), branch_num
    edges = G.subgraph(best_flexiclique).edges()
    len_edges = len(edges)
    return best_flexiclique, best_size, initial_best_size, len_edges, branch_num


def load_network(file_path):
    G = nx.Graph()
    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue

            parts = line.split()
            if len(parts) < 2:
                continue

            u, v = map(int, parts[:2])
            G.add_edge(u, v)
    return G

