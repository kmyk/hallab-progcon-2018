//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#include "Answer.hpp"

//------------------------------------------------------------------------------
namespace hpc {

using namespace std;

class solver {
public:
    Stage const & stage;
    solver(Stage const & stage_)
            : stage(stage_) {
    }

    Action decide_next_action(Stage const & stage_) {
        // 解答コードのサンプルです

        // 小さい生地の生地置き場にある、0番目の生地を対象として
        auto laneType = CandidateLaneType_Small;
        int pieceIndex = 0;
        const auto& piece = stage.candidateLane(laneType).pieces()[pieceIndex];

        // オーブンの原点に配置できそうなら、配置する
        Vector2i putPos(0, 0);
        if (stage.oven().isAbleToPut(piece, putPos)) {
            return Action::Put(laneType, pieceIndex, putPos);
        }

        // 配置できないなら、このターンは何もしない
        return Action::Wait();
    }
};

solver *g_solver = nullptr;


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
