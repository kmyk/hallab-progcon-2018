#include <algorithm>
#include <bitset>
#include <cassert>
#include <climits>
#include <functional>
#include <iostream>
#include <memory>
#include <numeric>
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
    constexpr int H = Parameter::OvenHeight;
    constexpr int W = Parameter::OvenWidth;
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

ostream & operator << (ostream & out, Vector2i const & pos) {
    return out << "(" << pos.x << ", " << pos.y << ")";
}
ostream & operator << (ostream & out, Action const & action) {
    if (action.isWaiting()) {
        return out << "Wait()";
    } else {
        const char *lane_type = (action.candidateLaneType() == CandidateLaneType_Small ? "Small" : "Large");
        return out << "Put(" << lane_type << ", " << action.pieceIndex() << ", " << action.putPos() << ")";
    }
}
ostream & operator << (ostream & out, Piece const & piece) {
    return out << "Piece(w = " << piece.width() << ", h = " << piece.height()
        // << ", t = " << piece.currentHeatTurnCount() << "/" << piece.requiredHeatTurnCount() << ")";
        << ", t = " << piece.restRequiredHeatTurnCount() << ")";
}
ostream & operator << (ostream & out, Oven const & oven) {
    out << "Oven({ ";
    for (auto const & piece : oven.bakingPieces()) {
        out << piece.pos() << ": " << piece << ", ";
    }
    return out << "})";
}

class oven_score_calculator {
    static constexpr int H = Parameter::OvenHeight;
    static constexpr int W = Parameter::OvenWidth;
    Oven const & oven;
    array<array<int16_t, W>, H> packed;
    int score;

public:
    oven_score_calculator(Oven const & oven_)
            : oven(oven_),
              packed(),
              score() {
        for (auto const & piece : oven.bakingPieces()) {
            int ly = piece.pos().y;
            int lx = piece.pos().x;
            int ry = ly + piece.height();
            int rx = lx + piece.width();
            int16_t t = piece.restRequiredHeatTurnCount() - 1;
            if (t <= 0) continue;
            assert (t >= 1);
            REP3 (y, ly, ry) {
                packed[y][lx] = t;
                packed[y][rx - 1] = t;
            }
            REP3 (x, lx, rx) {
                packed[ly][x] = t;
                packed[ry - 1][x] = t;
            }
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
            int16_t t = piece.restRequiredHeatTurnCount() - 1;
            if (t <= 0) continue;
            assert (t >= 1);
            if (rx < W) REP3 (y, ly, ry) {
                score += min(packed[y][rx], t);
            }
            if (ry < H) REP3 (x, lx, rx) {
                score += min(packed[ry][x], t);
            }
        }
    }

    int wait() const {
        return score;
    }

    int put(Piece const & piece, Vector2i const & pos) const {
        int ly = pos.y;
        int lx = pos.x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int16_t t = piece.requiredHeatTurnCount() - 1;
        assert (t >= 0);
        int delta = 0;
        if (ly == 0) delta += t * (rx - lx);
        if (ry == H) delta += t * (rx - lx);
        if (lx == 0) delta += t * (ry - ly);
        if (rx == W) delta += t * (ry - ly);
        delta += 10 * piece.height() * piece.width();
        if (lx - 1 >= 0) REP3 (y, ly, ry) delta += min(packed[y][lx - 1], t);
        if (ly - 1 >= 0) REP3 (x, lx, rx) delta += min(packed[ly - 1][x], t);
        if (rx < W) REP3 (y, ly, ry) delta += min(packed[y][rx], t);
        if (ry < H) REP3 (x, lx, rx) delta += min(packed[ry][x], t);
        return score + delta;
    }
};

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

shared_ptr<state_t> new_next_state(shared_ptr<state_t> const & a, Stage const & stage, Action const & action, oven_score_calculator const & calculator) {
    auto b = make_shared<state_t>(*a);

    if (action.isWaiting()) {  // 待つ
        b->score += calculator.wait();
    } else {  // 置く
        b->actions.emplace_back(b->turn, action);
        Piece piece = get_piece_from_action(stage, action);
        bool baked = b->oven.tryToBake(&piece, action.putPos());
        assert (baked);
        b->used |= 1u << action.pieceIndex();
        b->score += 100 * pow(piece.height() * piece.width(), 1.5);
        b->score += calculator.put(piece, action.putPos());
    }

    // 進める
    b->turn += 1;
    b->oven.bakeAndDiscard();

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
    constexpr int H = Parameter::OvenHeight;
    constexpr int W = Parameter::OvenWidth;
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
        REP (x, H - piece.width() + 1) {
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

vector<pair<int, Action> > do_large_beam_search(Stage const & stage) {
    constexpr int BEAM_DEPTH = 13;
    constexpr int BEAM_WIDTH = 9;
    static vector<shared_ptr<state_t> > cur, prv;
    static array<int, (1 << Parameter::CandidatePieceCount)> used_pieces = {};
    static unordered_set<uint64_t> used_oven;

    cur.push_back(new_initial_state(stage));
    shared_ptr<state_t> best = cur.front();
    for (int iteration = 0; iteration < BEAM_DEPTH; ++ iteration) {
        // 置いてみる
        cur.swap(prv);
        cur.clear();
        for (auto const & a : prv) {
            oven_score_calculator calculator(a->oven);
            cur.push_back(new_next_state(a, stage, Action::Wait(), calculator));
            REP (i, Parameter::CandidatePieceCount) if (not (a->used & (1u << i))) {
                auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
                iterate_all_puttable_pos(a->oven, piece, [&](Vector2i const & pos) {
                    auto action = Action::Put(CandidateLaneType_Large, i, pos);
                    cur.push_back(new_next_state(a, stage, action, calculator));
                });
            }
        }

        // 並べ替え
        sort(ALL(cur), [&](shared_ptr<state_t> const & a, shared_ptr<state_t> const & b) {
            return a->score > b->score;
        });
        if (best->score < cur.front()->score) {
            best = cur.front();
        }

        // 重複排除
        cur.swap(prv);
        cur.clear();
        int beam_width = max(3, BEAM_WIDTH - iteration);
        for (auto const & a : prv) {
            if (used_pieces[a->used] >= (beam_width >= 4 ? 2 : 1)) continue;
            uint64_t hash = hash_oven(a->oven);
            if (used_oven.count(hash)) continue;
            cur.push_back(a);
            used_pieces[a->used] += 1;
            used_oven.insert(hash);
            if ((int)cur.size() >= beam_width) break;
        }
        fill(ALL(used_pieces), 0);
        used_oven.clear();

        // 結果が確定してたら打ち切り
        if (not best->actions.empty() and best->actions.front().first == stage.turn()) {
            auto action = best->actions.front().second;
            bool all_same = true;
            for (auto const & a : cur) {
                if (a->actions.empty() or a->actions.front().second != action) {
                    all_same = false;
                    break;
                }
            }
            if (all_same) {
                break;
            }
        }
    }
    cur.clear();
    prv.clear();

    // 結果の取り出し
    return best->actions;
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

public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
        last_oven = pack_oven(stage_.oven());
    }

    Action decide_next_action(Stage const & stage_) {
        assert (&stage == &stage_);

        // 状況が変わってないなら省略
        if (not stage_.oven().isEmpty()) {
            auto packed_oven = pack_oven(stage_.oven());
            if (packed_oven == last_oven) {
                return Action::Wait();
            }
            last_oven = packed_oven;
        }

        // 置けるやつがひとつもないなら省略
        bool is_puttable = false;
        for (auto lane_type : { CandidateLaneType_Large, CandidateLaneType_Small }) {
            REP (i, Parameter::CandidatePieceCount) {
                if (is_puttable) break;
                auto const & piece = stage.candidateLane(lane_type).pieces()[i];
                iterate_all_puttable_pos(stage.oven(), piece, [&](Vector2i const & pos) {
                    is_puttable = true;
                });
            }
        }
        if (not is_puttable) {
            return Action::Wait();
        }

        // 大型クッキーについてビームサーチ
        auto actions = do_large_beam_search(stage);
        if (not actions.empty() and actions.front().first == stage.turn()) {
            return actions.front().second;
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
    return g_solver->decide_next_action(aStage);
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
