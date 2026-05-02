from dataclasses import dataclass, field
from dataclasses_json import dataclass_json, config
from typing import TypeVar
import numpy as np
from copy import copy
import tqdm
import random
import json
import numpy.typing as npt
import itertools as it
import networkx as nx
import subprocess as sub
import matplotlib.pyplot as plt
from matplotlib import animation


T = TypeVar("T", bound=npt.NBitBase)


@dataclass(frozen=True, eq=True, order=True, slots=True)
class BnDPVState:
    arr: tuple[int, ...]

    def __str__(self):
        return f"{self.arr}"


@dataclass_json
@dataclass(slots=True)
class VotingBnDGraphBuilder:
    """
    Voting Beneficial and Direct Graph Builder

    Attributes:
        vot_pref: list of voter weights  and their preferences
        candidates: list of score candidates
    """

    vot_pref: list[tuple[float, npt.NDArray[np.int32]]] = field(
        metadata=config(
            encoder=lambda x: [(w, arr.tolist()) for w, arr in x],
            decoder=lambda x: [(w, np.array(arr, dtype=np.int32)) for w, arr in x],
        )
    )
    candidates: list[float]

    def __init__(
        self,
        candidates: list[float],
        vot_pref: list[tuple[float, npt.NDArray[np.int32]]],
    ):
        assert len(candidates) > 0, "Must have at least one candidate"
        assert (
            all(map(lambda x: x >= 0, candidates)) > 0
        ), "All candidate scores must be positive"

        self.candidates = candidates
        for w, pref in vot_pref:
            assert w, "Must have a positive weight"
        self.vot_pref = vot_pref

    def determine_winner(self, state: BnDPVState) -> int:
        """
        Determine the winner of the current state

        :param state: state
        :return: candidate id
        """
        ck = np.array(self.candidates)
        for voter_id, cand in enumerate(state.arr):
            (w, _) = self.vot_pref[voter_id]
            ck[cand] += w
        return np.argmax(ck).item()

    def vertex_generator(self):
        return map(
            BnDPVState,
            it.product(
                *(range(len(self.candidates)) for _ in range(len(self.vot_pref)))
            ),
        )

    def edge_vertex_generator(
        self, src: BnDPVState
    ) -> list[tuple[int, int, BnDPVState]]:

        return [
            (
                i,
                (src.arr[i] + j) % len(self.candidates),
                BnDPVState(
                    arr=(
                        src.arr[:i]
                        + ((src.arr[i] + j) % len(self.candidates),)
                        + src.arr[i + 1 :]
                    ),
                ),
            )
            for (i, j) in it.product(
                range(len(self.vot_pref)), range(1, len(self.candidates))
            )
        ]

    def validate_edge(
        self, src: BnDPVState, dest: BnDPVState, voter: int, candidate: int
    ) -> bool:
        win_src = self.determine_winner(src)
        win_dest = self.determine_winner(dest)
        return (
            self.vot_pref[voter][1][win_src]
            < self.vot_pref[voter][1][win_dest]  # Beneficial
            and candidate == win_dest  # Direct
        )

    def transform_vec(self, st: BnDPVState):
        # arr = copy(self.candidates)
        # for voter_id, cand_id in enumerate(st.arr):
        #     arr[cand_id] += self.vot_pref[voter_id][0]
        # return (st, tuple(arr))
        return st

    def edge_list_generator(self):
        ret = []
        for src in self.vertex_generator():
            for v, c, dest in self.edge_vertex_generator(src):
                if self.validate_edge(src, dest, v, c):
                    ret.append((self.transform_vec(src), self.transform_vec(dest)))
        return ret

    def generate_graph(self):
        g = nx.digraph.DiGraph()
        g.add_edges_from(self.edge_list_generator())
        return g


def log(x, message=None):
    print(f"{message} {x}")
    return x


examples = [
    VotingBnDGraphBuilder(
        candidates=[0, 1, 2, 3],
        vot_pref=[
            (1, -1 * np.array([3, 2, 0, 1])),
            (2, -1 * np.array([2, 0, 1, 3])),
            (3, -1 * np.array([0, 1, 2, 3])),
        ],
    ),
    VotingBnDGraphBuilder(
        candidates=[0, 1, 2, 3],
        vot_pref=[
            (1, -1 * np.array([2, 3, 0, 1])),
            (2, -1 * np.array([1, 2, 3, 0])),
            (3, -1 * np.array([0, 1, 2, 3])),
        ],
    ),
]


def rand_generator():
    return VotingBnDGraphBuilder(
        candidates=[0, 1, 2, 3],
        vot_pref=[
            (1, -1 * np.random.permutation([0, 1, 2, 3])),
            (2, -1 * np.random.permutation([0, 1, 2, 3])),
            (3, -1 * np.random.permutation([0, 1, 2, 3])),
        ],
    )


def check_empty(p1, p2, p3) -> bool:
    g = VotingBnDGraphBuilder(
        candidates=[0, 1, 2, 3],
        vot_pref=[
            (1, -1 * np.array(p1)),
            (2, -1 * np.array(p2)),
            (3, -1 * np.array(p3)),
        ],
    ).generate_graph()
    g = gen_graph(g)
    return len(g.nodes) >= 1


def gen_graph(g):
    while True:
        filt = [
            node
            for node in g.nodes()
            if g.in_degree(node) == 0 or g.out_degree(node) == 0
        ]
        if len(filt) == 0:
            break
        g.remove_nodes_from(filt)
    return g


def main_3d():
    js = None
    with open("output.json", "r") as f:
        js = f.read()
    data = json.loads(js)
    states: list[nx.Graph] = [
        gen_graph(VotingBnDGraphBuilder.from_dict(d).generate_graph()) for d in data
    ]

    g = random.choice(states)

    pos = nx.spring_layout(G=g, k=1, dim=3, iterations=100)
    point_size = 100

    plt.style.use("dark_background")
    # Create figure
    fig = plt.figure(figsize=(10, 10))

    ax = fig.add_subplot(111, projection="3d")

    # Draw edges with arrows
    for edge in g.edges():
        x = np.array([pos[edge[0]][0], pos[edge[1]][0]])
        y = np.array([pos[edge[0]][1], pos[edge[1]][1]])
        z = np.array([pos[edge[0]][2], pos[edge[1]][2]])
        #
        # # Draw line
        # ax.plot(x, y, z, "gray", linewidth=2, alpha=0.6)

        # Direction vector
        dx = x[1] - x[0]
        dy = y[1] - y[0]
        dz = z[1] - z[0]
        # Label showing "source→dest"
        ax.quiver(
            x[0],
            y[0],
            z[0],
            dx,
            dy,
            dz,
            color="red",  # Change color per edge if needed
            arrow_length_ratio=0.2,
            linewidth=3,
            alpha=0.4,
        )

    # Draw nodes
    for node, (x, y, z) in pos.items():
        ax.text(
            x,
            y,
            z,
            str(node),
            fontsize=10,
            ha="center",
            va="center",
            weight="bold",
        )
        ax.scatter(
            x, y, z, s=500, c="lightblue", edgecolors="black", linewidths=2, alpha=0.5
        )

    # Styling
    ax.set_axis_off()
    ax.set_title("Interactive 3D Directed Graph", fontsize=16)

    # Enable interactive mode
    plt.tight_layout()
    plt.show()  # This opens an interactive window you can rotate/zoom


if __name__ == "__main__":
    # main()
    main_3d()
