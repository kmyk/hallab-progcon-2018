//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
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
    bitset<H * W> packed;
    REP (y, H) REP (x, W) {
        if (oven.isAbleToPut(1, 1, Vector2i(x, y))) {
            packed.set(y * W + x);
        }
    }
    return hash<bitset<H * W> >()(packed);
}

int get_oven_score(Oven const & oven) {
    constexpr int H = Parameter::OvenHeight;
    constexpr int W = Parameter::OvenWidth;
    array<array<int, W>, H> packed = {};
    int score = 0;
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int t = piece.restRequiredHeatTurnCount();
        REP3 (y, ly, ry) {
            packed[y][lx] = t;
            packed[y][rx - 1] = t;
        }
        REP3 (x, lx, rx) {
            packed[ly][x] = t;
            packed[ry - 1][x] = t;
        }
        score += 100 * piece.height() * piece.width();
    }
    for (auto const & piece : oven.bakingPieces()) {
        int ly = piece.pos().y;
        int lx = piece.pos().x;
        int ry = ly + piece.height();
        int rx = lx + piece.width();
        int t = piece.restRequiredHeatTurnCount();
        REP3 (y, ly, ry) {
            if (lx - 1 >= 0) score -= abs(packed[y][lx - 1] - t);
            if (rx     <  W) score -= abs(packed[y][rx    ] - t);
        }
        REP3 (x, lx, rx) {
            if (ly - 1 >= 0) score -= abs(packed[ly - 1][x] - t);
            if (ry     <  H) score -= abs(packed[ry    ][x] - t);
        }
    }
    return score;
}

struct state_t {
    Oven oven;
    vector<pair<int, Action> > actions;
    array<bool, Parameter::CandidatePieceCount> used;
    int turn;
    double score;
};

Piece const & get_piece_from_action(Stage const & stage, Action const & action) {
    return stage.candidateLane(action.candidateLaneType()).pieces()[action.pieceIndex()];
}

bool is_intersect(Vector2i const & pos1, Piece const & piece1, Vector2i const & pos2, Piece const & piece2) {
    return Util::IsIntersect(
        pos1, piece1.width(), piece1.height(),
        pos2, piece2.width(), piece2.height());
}

shared_ptr<state_t> apply_action(shared_ptr<state_t> const & a, Stage const & stage, Action const & action) {
    auto b = make_shared<state_t>(*a);

    if (not action.isWaiting()) {  // 置く
        b->actions.emplace_back(b->turn, action);
        Piece piece = get_piece_from_action(stage, action);
        bool baked = b->oven.tryToBake(&piece, action.putPos());
        assert (baked);
        b->used[action.pieceIndex()] = true;
    }

    // 進める
    b->turn += 1;
    b->oven.bakeAndDiscard();
    b->score += get_oven_score(b->oven);

    // 腐らせる
    REP (i, Parameter::CandidatePieceCount) if (not b->used[i]) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
        b->used[i] = (b->turn + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit);
    }
    return b;
}


vector<pair<int, Action> > do_large_beam_search(Stage const & stage) {
    constexpr int BEAM_DEPTH = 30;
    constexpr int BEAM_WIDTH = 20;
    vector<shared_ptr<state_t> > cur, prv;
    array<int, (1 << Parameter::CandidatePieceCount)> used_pieces = {};
    unordered_set<uint64_t> used_oven;

    {  // 初期化
        auto a = make_shared<state_t>();
        a->oven = stage.oven();
        REP (i, Parameter::CandidatePieceCount) {
            auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
            a->used[i] = (stage.turn() + piece.requiredHeatTurnCount() >= Parameter::GameTurnLimit);
        }
        a->turn = stage.turn();
        a->score = 0;
        if (not count(ALL(a->used), false)) {
            return a->actions;
        }
        cur.push_back(a);
    }

    shared_ptr<state_t> best = cur.front();
    for (int iteration = 0; iteration < BEAM_DEPTH; ++ iteration) {
        // 置いてみる
        cur.swap(prv);
        cur.clear();
        for (auto const & a : prv) {
            REP (i, Parameter::CandidatePieceCount) if (not a->used[i]) {
                auto const & piece = stage.candidateLane(CandidateLaneType_Large).pieces()[i];
                REP (y, Parameter::OvenHeight) {
                    REP (x, Parameter::OvenWidth) {
                        Vector2i p(x, y);
                        if (a->oven.isAbleToPut(piece, p)) {
                            auto action = Action::Put(CandidateLaneType_Large, i, p);
                            cur.push_back(apply_action(a, stage, action));
                        }
                    }
                }
            }
        }
        if (cur.empty()) break;  // まったく置くところないなら終了

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
        for (auto const & a : prv) {
            uint8_t pieces = 0;
            REP (i, Parameter::CandidatePieceCount) {
                if (a->used[i]) pieces |= 1u << i;
            }
            if (pieces == -1) continue;
            if (used_pieces[pieces] >= 10) continue;
            uint64_t hash = hash_oven(a->oven);
            if (used_oven.count(hash)) continue;
            cur.push_back(a);
            used_pieces[pieces] += 1;
            used_oven.insert(hash);
            if (cur.size() >= BEAM_WIDTH) break;
        }
        fill(ALL(used_pieces), 0);
        used_oven.clear();
    }

    // 結果の取り出し
    return best->actions;
}

Action do_small_greedy(Stage const & stage, vector<pair<int, Action> > const & actions) {
    Action best_action = Action::Wait();
    int best_score = INT_MIN;

    REP (i, Parameter::CandidatePieceCount) {
        auto const & piece = stage.candidateLane(CandidateLaneType_Small).pieces()[i];
        REP (y, Parameter::OvenHeight) {
            REP (x, Parameter::OvenWidth) {
                Vector2i p(x, y);

                // 置けるかどうか確認
                if (not stage.oven().isAbleToPut(piece, p)) continue;
                bool conflicted = false;
                for (auto const & it : actions) {
                    if (stage.turn() + piece.requiredHeatTurnCount() < it.first + 3) break;
                    auto const & action = it.second;
                    if (is_intersect(p, piece, action.putPos(), get_piece_from_action(stage, action))) {
                        conflicted = true;
                        break;
                    }
                }
                if (conflicted) continue;

                // 置いてみる
                auto action = Action::Put(CandidateLaneType_Small, i, p);
                Oven oven = stage.oven();
                Piece piece1 = piece;
                bool baked = oven.tryToBake(&piece1, p);
                assert (baked);
                int score = 0;
                REP (iteration, 5) {
                    oven.bakeAndDiscard();
                    score += get_oven_score(oven);
                }
                if (best_score < score) {
                    best_score = score;
                    best_action = action;
                }
            }
        }
    }

    return best_action;
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
    cerr << "[*] stage = " << (++ g_stage) << endl;
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
    if (aStage.turn() <= 5 or aStage.turn() % 50 == 0 or aStage.turn() >= 998) {
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
