#include <algorithm>
#include <bitset>
#include <cassert>
#include <climits>
#include <functional>
#include <iostream>
#include <memory>
#include <numeric>
#include <random>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include "Answer.hpp"
#define REP(i, n) for (int i = 0; (i) < (int)(n); ++ (i))
#define REP3(i, m, n) for (int i = (m); (i) < (int)(n); ++ (i))
#define REP_R(i, n) for (int i = int(n) - 1; (i) >= 0; -- (i))
#define REP3R(i, m, n) for (int i = int(n) - 1; (i) >= (int)(m); -- (i))
#define ALL(x) begin(x), end(x)
typedef long long ll;
template <class T, class U> inline void chmax(T & a, U const & b) { a = std::max<T>(a, b); }
template <class T, class U> inline void chmin(T & a, U const & b) { a = std::min<T>(a, b); }

//------------------------------------------------------------------------------
namespace hpc {

using namespace std;

constexpr int H = Parameter::OvenHeight;
constexpr int W = Parameter::OvenWidth;
constexpr int K = Parameter::CandidatePieceCount;

class xor_shift_128 {
public:
    typedef uint32_t result_type;
    xor_shift_128(uint32_t seed = 42) {
        set_seed(seed);
    }
    void set_seed(uint32_t seed) {
        a = seed = 1812433253u * (seed ^ (seed >> 30));
        b = seed = 1812433253u * (seed ^ (seed >> 30)) + 1;
        c = seed = 1812433253u * (seed ^ (seed >> 30)) + 2;
        d = seed = 1812433253u * (seed ^ (seed >> 30)) + 3;
    }
    uint32_t operator() () {
        uint32_t t = (a ^ (a << 11));
        a = b; b = c; c = d;
        return d = (d ^ (d >> 19)) ^ (t ^ (t >> 8));
    }
    static constexpr uint32_t max() { return numeric_limits<result_type>::max(); }
    static constexpr uint32_t min() { return numeric_limits<result_type>::min(); }
private:
    uint32_t a, b, c, d;
};

typedef array<uint32_t, Parameter::OvenHeight> packed_oven_t;
packed_oven_t pack_oven(Oven const & oven) {
    static_assert (Parameter::OvenWidth < CHAR_BIT * sizeof(uint32_t), "");
    packed_oven_t a = {};
    REP (y, Parameter::OvenHeight) {
        REP (x, Parameter::OvenWidth) {
            if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
                a[y] |= 1u << x;
            }
        }
    }
    return a;
}

uint64_t hash_oven(Oven const & oven) {
#ifdef DEBUG
    // デバッグの都合で bitset を避けたい
    string s(H * W / CHAR_BIT, '\0');
    REP (y, H) REP (x, W) {
        if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
            int z = y * W + x;
            s[z / 8] |= 1u << (z % 8);
        }
    }
    return hash<string>()(s);
#else
    // ちょっとだけ速い気がする
    bitset<H * W> packed;
    REP (y, H) REP (x, W) {
        if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
            packed.set(y * W + x);
        }
    }
    return hash<bitset<H * W> >()(packed);
#endif
}

int get_oven_score(Oven const & oven) {
    array<array<int16_t, W>, H> packed = {};
    int score = 0;
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int16_t t = piece.restRequiredHeatTurnCount();
        assert (t >= 1);
        REP3 (y, ly, ry) packed[y][lx] = t;
        REP3 (x, lx, rx) packed[ly][x] = t;
        if (ly == 0) score += t * (rx - lx);
        if (ry == H) score += t * (rx - lx);
        if (lx == 0) score += t * (ry - ly);
        if (rx == W) score += t * (ry - ly);
        score += 10 * piece.height() * piece.width();
    }
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int16_t t = piece.restRequiredHeatTurnCount();
        if (rx < W) REP3 (y, ly, ry) {
            score += min(packed[y][rx], t);
        }
        if (ry < H) REP3 (x, lx, rx) {
            score += min(packed[ry][x], t);
        }
    }
    return score;
}

struct state_t {
    Oven oven;
    vector<pair<int, Action> > actions;
    uint8_t used;
    int turn;
    ll score;
};

Piece const & get_piece_from_action(Stage const & stage, Action const & action) {
    return stage.candidateLane(action.candidateLaneType()).pieces()[action.pieceIndex()];
}

bool is_intersect(Vector2i const & pos1, Piece const & piece1, Vector2i const & pos2, Piece const & piece2) {
    return Util::IsIntersect(
        pos1, piece1.width(), piece1.height(),
        pos2, piece2.width(), piece2.height());
}

shared_ptr<state_t> new_initial_state(Stage const & stage) {
    auto a = make_shared<state_t>();
    a->oven = stage.oven();
    a->used = 0;
    REP (i, Parameter::CandidatePieceCount) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        if (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) {
            a->used |= 1u << i;
        }
    }
    a->turn = stage.turn();
    a->score = 0;
    return a;
}

shared_ptr<state_t> new_next_state(shared_ptr<state_t> const & a, Stage const & stage, Action const & action) {
    auto b = make_shared<state_t>(*a);

    if (not action.isWaiting()) {  // 置く
        b->actions.emplace_back(b->turn, action);
        Piece piece = get_piece_from_action(stage, action);
        bool baked = b->oven.tryToBake(&piece, action.putPos());
        assert (baked);
        b->used |= 1u << action.pieceIndex();
        b->score += 100 * pow(piece.height() * piece.width(), 1.5);
    }

    // 進める
    b->turn += 1;
    b->oven.bakeAndDiscard();
    b->score += get_oven_score(b->oven);

    // 腐らせる
    REP (i, Parameter::CandidatePieceCount) if (not (b->used & (1u << i))) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        if (b->turn + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) {
            b->used |= 1u << i;
        }
    }
    return b;
}

template <typename Func>
void iterate_all_puttable_pos(Oven const & oven, Piece const & piece, Func func) {
    array<array<char, W + 1>, H + 1> imos = {};
    for (auto const & baking : oven.bakingPieces()) {
        int ly = baking.pos().y;
        int lx = baking.pos().x;
        int ry = ly + baking.height();
        int rx = lx + baking.width();
        ly = max(0, ly - piece.height() + 1);
        lx = max(0, lx - piece.width() + 1);
        imos[ly][lx] += 1;
        imos[ly][rx] -= 1;
        imos[ry][lx] -= 1;
        imos[ry][rx] += 1;
    }
    REP (y, H - piece.height() + 1) {
        REP (x, W - piece.width() + 1) {
            imos[y    ][x + 1] += imos[y][x];
            imos[y + 1][x    ] += imos[y][x];
            imos[y + 1][x + 1] -= imos[y][x];
            if (not imos[y][x]) {
                func(Vector2i(x, y));
            }
        }
    }
}

bool operator == (Action const & a, Action const & b) {
    if (a.isWaiting() or b.isWaiting()) {
        return a.isWaiting() == b.isWaiting();
    } else {
        return make_tuple(a.candidateLaneType(), a.pieceIndex(), a.putPos())
            == make_tuple(b.candidateLaneType(), b.pieceIndex(), b.putPos());
    }
}
bool operator != (Action const & a, Action const & b) {
    return not (a == b);
}

void fill_rest_hest_turn(Oven const & oven, array<array<int16_t, W>, H> & rest_heat_turn) {
    REP (y, H) REP (x, W) rest_heat_turn[y][x] = 0;
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int16_t t = piece.restRequiredHeatTurnCount();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            rest_heat_turn[y][x] = t;
        }
    }
}

void fill_puttable_t(Stage const & stage, array<array<array<int16_t, W>, H>, K> & puttable_t) {
    // TODO: O(KHWb) から O(Kb + KHW) にできる
    REP (i, K) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        REP (y, H) REP (x, W) puttable_t[i][y][x] = INT16_MAX;
        if (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit) continue;
        REP (y, H - piece.height() + 1) REP (x, W - piece.width() + 1) {
            puttable_t[i][y][x] = 0;
            for (auto const & baking : stage.oven().bakingPieces()) {
                if (is_intersect(Vector2i(x, y), piece, baking.pos(), baking)) {
                    chmax(puttable_t[i][y][x], baking.restRequiredHeatTurnCount() + 1);
                }
            }
        }
    }
}

void list_puttable_pos(Stage const & stage, array<array<array<int16_t, W>, H>, K> const & puttable_t, int DEPTH, array<vector<pair<int8_t, int8_t> >, K> & puttable_pos) {
    REP (i, K) {
        puttable_pos[i].clear();
        REP (y, H) REP (x, W) {
            if (puttable_t[i][y][x] < DEPTH) {
                puttable_pos[i].emplace_back(y, x);
            }
        }
    }
}

vector<pair<int, Action> > do_large_simulated_annealing(Stage const & stage) {
    constexpr int DEPTH = 20;
    static xor_shift_128 gen;

    static array<array<int16_t, W>, H> rest_heat_turn;
    fill_rest_hest_turn(stage.oven(), rest_heat_turn);

    static array<array<array<int16_t, W>, H>, K> puttable_t;
    fill_puttable_t(stage, puttable_t);

    static array<vector<pair<int8_t, int8_t> >, K> puttable_pos;
    list_puttable_pos(stage, puttable_t, DEPTH, puttable_pos);

    auto get_score = [&](array<pair<int, Action>, K> const & cur, array<array<int8_t, H>, W> const & used) {
        vector<pair<int, double> > scores;
        REP (i, K) if (cur[i].first != -1) {
            auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
            int ly = cur[i].second.putPos().y;
            int lx = cur[i].second.putPos().x;
            int ry = ly + piece.height();
            int rx = lx + piece.width();
            int t0 = cur[i].first;
            int t = piece.requiredHeatTurnCount();
            double score = 0;
            score += pow(piece.height() * piece.width(), 1.3);
            auto touch = [&](int y, int x) -> double{
                if (rest_heat_turn[y][x]) {
                    return max(0, min<int>(rest_heat_turn[y][x], t + t0) - t0);
                } else {
                    int j = used[y][x];
                    if (j == -1) return 0;
                    auto const & piece_ = stage.candidateLane(CandidateLaneType_Large).pieces()[j];
                    int t0_ = cur[j].first;
                    int t_ = piece_.requiredHeatTurnCount();
                    return exp(- t0_ / 10.0) * max(0, min<int>(t0 + t, t0_ + t_) - max(t0, t0_));
                }
            };
            if (lx == 0) score += t * (ry - ly);
            if (lx != 0) REP3 (y, ly, ry) touch(y, lx - 1);
            if (ly == 0) score += t * (rx - lx);
            if (ly != 0) REP3 (x, lx, rx) touch(ly - 1, x);
            if (rx == W) score += t * (ry - ly);
            if (rx != W) REP3 (y, ly, ry) touch(y, rx);
            if (ry == H) score += t * (rx - lx);
            if (ry != H) REP3 (x, lx, rx) touch(ry, x);
            scores.emplace_back(t0, score);
        }
        double sum_score = 0;
        sort(ALL(scores));
        REP (i, scores.size()) {
            int t0; double score; tie(t0, score) = scores[i];
            sum_score += score * exp(- t0 / 5.0);
        }
        return sum_score;
    };

    auto remove = [&](array<pair<int, Action>, K> & cur, array<array<int8_t, H>, W> & used, int i) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        int ly = cur[i].second.putPos().y;
        int lx = cur[i].second.putPos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            used[y][x] = 0;
        }
        cur[i].first = -1;
    };

    auto add = [&](array<pair<int, Action>, K> & cur, array<array<int8_t, H>, W> & used, int i, int ly, int lx) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        if (cur[i].first != -1) {
            remove(cur, used, i);
        }
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        REP3 (y, ly, ry) REP3 (x, lx, rx) {
            if (used[y][x] != -1) {
                remove(cur, used, used[y][x]);
            }
            used[y][x] = i;
        }
        cur[i].first = puttable_t[i][ly][lx];
        cur[i].second = Action::Put(CandidateLaneType_Large, i, Vector2i(lx, ly));
    };

    array<pair<int, Action>, K> cur;
    fill(ALL(cur), make_pair(-1, Action::Wait()));
    ll score = 0;
    array<array<int8_t, H>, W> used = {};
    REP (y, H) REP (x, W) used[y][x] = -1;

    auto result = cur;
    auto highscore = score;
    constexpr int ITERATION = 16384;
    REP (iteration, ITERATION) {
        int i = uniform_int_distribution<int>(0, K - 1)(gen);
        if (puttable_pos[i].empty()) continue;  // TODO: 事前にはじく

        int ly, lx;
        if (cur[i].first == -1 or bernoulli_distribution(0.3)(gen)) {
            tie(ly, lx) = puttable_pos[i][uniform_int_distribution<int>(0, puttable_pos[i].size() - 1)(gen)];
        } else {
            static const int table_dy[4] = { -1, 1, 0, 0 };
            static const int table_dx[4] = { 0, 0, 1, -1 };
            int dir = uniform_int_distribution<int>(0, 3)(gen);
            int k = uniform_int_distribution<int>(1, 3)(gen);
            ly = cur[i].second.putPos().y + k * table_dy[dir];
            lx = cur[i].second.putPos().x + k * table_dx[dir];
            if (ly < 0 or H <= ly) continue;
            if (lx < 0 or W <= lx) continue;
            if (puttable_t[i][ly][lx] == INT16_MAX) continue;
        }

        array<pair<int, Action>, K> nxt = cur;
        array<array<int8_t, H>, W> next_used = used;
        add(nxt, next_used, i, ly, lx);

        ll next_score = get_score(nxt, next_used);
        ll delta = next_score - score;
        double temperature = (double)(ITERATION - iteration) / ITERATION;
        constexpr double BOLTZMANN = 0.01;
        if (0 <= delta or bernoulli_distribution(exp(BOLTZMANN * delta / temperature))(gen)) {
            score += delta;
            cur = nxt;
            used = next_used;
            if (highscore < score) {
                highscore = score;
                result = cur;
            }
        }
    }

    vector<pair<int, Action> > actions;
    REP (i, K) if (result[i].first != -1) {
        result[i].first += stage.turn();
        actions.push_back(result[i]);
    }
    sort(ALL(actions), [&](pair<int, Action> const & a, pair<int, Action> const & b) {
        return a.first < b.first;
    });
    return actions;
}

Action do_small_greedy(Stage const & stage, vector<pair<int, Action> > const & actions) {
    array<int, Parameter::CandidatePieceCount> order;
    iota(ALL(order), 0);
    sort(ALL(order), [&](int i, int j) {
        auto const & p = stage.candidateLane(CandidateLaneType_Small).pieces()[i];
        auto const & q = stage.candidateLane(CandidateLaneType_Small).pieces()[j];
        return p.height() * p.width() > q.height() * q.width();
    });
    for (int i : order) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Small).pieces()[i];
        bool found = false;
        Vector2i found_pos;
        iterate_all_puttable_pos(stage.oven(), piece, [&](Vector2i const & pos) {
            if (found) return;

            // 大型クッキーの予定と整合するか確認
            for (auto const & it : actions) {
                if (stage.turn() + piece.requiredHeatTurnCount() < it.first) break;
                auto const & action = it.second;
                if (is_intersect(pos, piece, action.putPos(), get_piece_from_action(stage, action))) {
                    return;
                }
            }

            found = true;
            found_pos = pos;
        });

        if (found) {
            return Action::Put(CandidateLaneType_Small, i, found_pos);
        }
    }

    return Action::Wait();
}

class solver {
    packed_oven_t last_oven;
    vector<pair<int, Action> > actions;

public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
        last_oven = pack_oven(stage_.oven());
    }

    Action decide_next_action(Stage const & stage_) {
        assert (&stage == &stage_);

        // // 状況が変わってないなら省略
        // if (not stage_.oven().isEmpty()) {
        //     auto packed_oven = pack_oven(stage_.oven());
        //     if (packed_oven == last_oven) {
        //         return Action::Wait();
        //     }
        //     last_oven = packed_oven;
        // }

        // // 置けるやつがひとつもないなら省略
        // bool is_puttable = false;
        // for (auto lane_type : { CandidateLaneType_Large, CandidateLaneType_Small }) {
        //     REP (i, Parameter::CandidatePieceCount) {
        //         if (is_puttable) break;
        //         auto const & piece = stage.candidateLane(lane_type).pieces()[i];
        //         iterate_all_puttable_pos(stage.oven(), piece, [&](Vector2i const & pos) {
        //             is_puttable = true;
        //         });
        //     }
        // }
        // if (not is_puttable) {
        //     return Action::Wait();
        // }

        // 大型クッキーについて焼き鈍し
        if (actions.empty()) {
            actions = do_large_simulated_annealing(stage);
        }
        assert (actions.empty() or actions.front().first >= stage.turn());
        if (not actions.empty() and actions.front().first == stage.turn()) {
            auto action = actions.front().second;
            actions.clear();
            return action;
        }

        // 小型クッキーは貪欲
        auto action = do_small_greedy(stage, actions);
        if (not action.isWaiting()) return action;

        return Action::Wait();
    }
};

solver *g_solver = nullptr;
#ifdef LOCAL
int g_stage = 0;
int g_score = 0;
#endif


//------------------------------------------------------------------------------
/// コンストラクタ。
/// @detail 最初のステージ開始前に実行したい処理があればここに書きます。
Answer::Answer()
{
}

//------------------------------------------------------------------------------
/// デストラクタ。
/// @detail 最後のステージ終了後に実行したい処理があればここに書きます。
Answer::~Answer()
{
}

//------------------------------------------------------------------------------
/// 各ステージ開始時に呼び出される処理。
/// @detail 各ステージに対する初期化処理が必要ならここに書きます。
/// @param aStage 現在のステージ。
void Answer::init(const Stage& aStage)
{
#ifdef LOCAL
    cerr << "[*] stage = " << (g_stage ++) << endl;
    g_score = 0;
#endif
    g_solver = new solver(aStage);
}

//------------------------------------------------------------------------------
/// このターンでの行動を指定する。
/// @detail 希望する行動を Action の static 関数で生成して return してください。
///         正常ではない行動を return した場合、何も起きません。
///         詳細は Action のヘッダを参照してください。
/// @param aStage 現在のステージ。
Action Answer::decideNextAction(const Stage& aStage)
{
#ifdef LOCAL
    for (auto const & piece : aStage.oven().lastBakedPieces()) {
        g_score += piece.score();
    }
    if (aStage.turn() % 50 == 0 or aStage.turn() >= 999) {
        cerr << "[*] turn = " << aStage.turn() << ": score = " << g_score << endl;
    }
#endif
    auto action = g_solver->decide_next_action(aStage);
    if (not action.isWaiting()) {
        auto const & piece = get_piece_from_action(aStage, action);
        assert (aStage.oven().isAbleToPut(piece, action.putPos()));
    }
    return action;
}

//------------------------------------------------------------------------------
/// 各ステージ終了時に呼び出される処理。
/// @detail 各ステージに対する終了処理が必要ならここに書きます。
/// @param aStage 現在のステージ。
void Answer::finalize(const Stage& aStage)
{
    delete g_solver;
    g_solver = nullptr;
}

} // namespace
// EOF
