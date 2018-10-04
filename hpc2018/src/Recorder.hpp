//------------------------------------------------------------------------------
/// @file
/// @author   ハル研究所プログラミングコンテスト実行委員会
///
/// @copyright  Copyright (c) 2018 HAL Laboratory, Inc.
/// @attention  このファイルの利用は、同梱のREADMEにある
///             利用条件に従ってください。
//------------------------------------------------------------------------------
#pragma once

//------------------------------------------------------------------------------
#include "FieldType.hpp"
#include "Stage.hpp"

//------------------------------------------------------------------------------
namespace hpc {

/// ゲーム進行を記録するクラス。
class Recorder
{
public:
    /// @name コンストラクタ
    //@{
    Recorder();
    //@}

    /// @name ダンプ
    //@{
    /// 記録内容を JSON として出力する。
    void dumpJson() const;
    /// 最終結果を出力する。
    void dumpResult(bool aIsSilent) const;
    //@}

    /// @name 記録
    //@{
    /// ステージの初期化後に実行される関数。
    void afterInitStage(const Stage& aStage);
    /// ターンを進めた後に実行される関数。
    void afterAdvanceTurn(const Stage& aStage);
    /// ステージが終了した後に実行される関数。
    void afterFinishStage();
    /// 全ステージが終了した後に実行される関数。
    void afterFinishAllStages();
    //@}

    /// @name 問い合わせ
    //@{
    /// ゲーム全体での総ターン数。
    int totalTurn() const;
    /// ゲーム全体での総スコア。
    int totalScore() const;
    //@}

private:
    /// @name 内部構造体
    //@{
    /// 生地情報。
    struct PieceRecord
    {
        /// 置かれているフィールド。
        char fieldType;
        /// 置いた場所。
        char posX;
        char posY;
        /// 横幅。
        char width;
        /// 縦幅。
        char height;
        /// 現在までに与えられた加熱ターン数。
        short currentHeatTurnCount;
        /// 完成に必要な加熱ターン数。
        short requiredHeatTurnCount;
        /// 完成で得られるスコア。
        short score;

        /// 情報を埋める。
        PieceRecord& setup(const Oven* aOven, const Piece& aPiece);

        /// Jsonで情報を出力する。
        void dumpJson() const;
    };
    /// オーブン設定情報
    struct OvenRecipeRecord
    {
        /// 横幅。
        int width;
        /// 縦幅。
        int height;
    };
    /// オーブン情報。
    struct OvenRecord
    {
        /// 1ターンで記録する最大生地数。
        static const int MaxOvenedPieceCount = 60;
        /// このターンに焼いている生地一覧。
        PieceRecord prvBakingPieces[MaxOvenedPieceCount];
        /// prvBakingPieces の有効な要素数。
        int bakingPieceCount;
        /// このターンに焼き上がった生地一覧。
        PieceRecord prvBakedPieces[MaxOvenedPieceCount];
        /// prvBakedPieces の有効な要素数。
        int bakedPieceCount;
        /// このターンにこのオーブンが計上したスコア。
        int turnScore;

        /// prvBakingPieces へのアクセサ。
        PieceRecord& bakingPieces(int aIndex);
        /// prvBakingPieces へのアクセサ。
        const PieceRecord& bakingPieces(int aIndex) const;
        /// prvBakedPieces へのアクセサ。
        PieceRecord& bakedPieces(int aIndex);
        /// prvBakedPieces へのアクセサ。
        const PieceRecord& bakedPieces(int aIndex) const;
    };
    /// ターン情報。
    struct TurnRecord
    {
        /// 生地置き場の記録。
        PieceRecord candidateLane[CandidateLaneType_TERM][Parameter::CandidatePieceCount];
        /// 生地置き場の生地数。
        int candidatePieceCount[CandidateLaneType_TERM];
        /// オーブン情報。
        OvenRecord ovenRecord;
        /// このターンで稼いだスコア。
        int turnScore;
        /// このターン終了時のステージスコア。
        int turnEndScore;
    };
    /// ステージ情報。
    struct StageRecord
    {
        /// スコア。
        int score;
        /// オーブン設定。
        OvenRecipeRecord ovenRecipeRecord;
        /// ターン情報。
        TurnRecord turnRecords[Parameter::GameTurnLimit + 1];
        /// 有効なターン情報の数。
        int turnRecordCount;

        /// ターン数。
        /// @attention turnRecordCount != ターン数、です。
        ///            これは turnRecord[0] にステージ開始時の盤面が入っているためです。
        int turn() const;
    };
    /// ゲーム情報。
    struct GameRecord
    {
        /// ゲーム全体での総ターン数。
        int totalTurn;
        /// ゲーム全体での総スコア。
        int totalScore;
        /// ステージ情報。
        StageRecord stageRecords[Parameter::GameStageCount];
    };
    //@}

    /// @name 内部実装
    //@{
    /// ステージ情報を JSON として出力する。
    void dumpJsonStage(const StageRecord& aRecord) const;
    /// ターン情報を JSON として出力する。
    void dumpJsonTurn(const TurnRecord& aRecord) const;
    /// 現在のターン情報を記録する。
    void writeTurnRecord(int aStageNumber, int aTurn, const Stage& aStage);
    //@}

    /// @name プライベートメンバ変数
    //@{
    /// ゲーム情報。
    GameRecord mGameRecord;
    /// 今記録中のステージ番号。
    int mCurrentStageNumber;
    /// 今記録中のターン番号。
    /// @attention 初期盤面がターン番号 0 であることに注意が必要です。
    ///            つまりプレイヤーが初めて干渉したときの盤面は
    ///            ターン番号 1 で記録されます。
    ///            これはターン数を 0 オリジンで考えたときに
    ///            ターン番号と現在のターン数が一致しないことを意味します。
    int mCurrentTurn;
    /// 今記録中のスコア。
    int mCurrentScore;
    //@}
};

} // namespace
// EOF
