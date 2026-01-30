from dataclasses import dataclass
import array as ar
import networkx as nx


@dataclass(frozen=True, eq=True, order=True, slots=True)
class BnDPVState:
    arr: tuple[int, ...]


@dataclass(slots=True)
class VotingBnDGraphBuilder:
    """
    Voting Beneficial and Direct Graph Builder

    Attributes:
        vot_pref: list of voter weights  and their preferences
        candidates: list of score candidates
    """

    vot_pref: list[tuple[float, ar.array[int]]]
    candidates: list[float]

    def __init__(
        self,
        vot_pref: list[tuple[float, ar.array[int]]],
        candidates: list[float],
    ):
        assert len(candidates) > 0, "Must have at least one candidate"
        assert (
            all(map(lambda x: x >= 0, candidates)) > 0
        ), "All candidate scores must be positive"

        self.candidates = candidates
        for w, pref in self.vot_pref:
            assert w, "Must have a positive weight"
            assert all(
                (c in range(len(candidates)) for c in pref)
            ), "Include only valid candidates"
            assert len(set(pref)) == pref, "Must include all candidates"
        self.vot_pref = vot_pref

    def determine_winner(self, state: BnDPVState):
        ls: list[int] = [0]* len(self.vot_pref)
        ck = ar.array.fromList()
        for (voter_id, cand) in state.arr:

    def edge_list_generator(self):
        pass

    def generate_graph(self):
        pass
