
# ===================================================================
# インクルードパスの設定
# ===================================================================


# ===================================================================
# サブディレクトリの設定
# ===================================================================


# ===================================================================
#  ソースファイルの設定
# ===================================================================



set ( DATA_DIR ${CMAKE_CURRENT_SOURCE_DIR}/../testdata/ )

# ===================================================================
#  テスト用のターゲットの設定
# ===================================================================

ym_add_gtest ( fraig_FraigMgr_test
  fraig_test.cc
  $<TARGET_OBJECTS:ym_base_obj_d>
  $<TARGET_OBJECTS:ym_logic_obj_d>
  $<TARGET_OBJECTS:ym_sat_obj_d>
  $<TARGET_OBJECTS:ym_cell_obj_d>
  $<TARGET_OBJECTS:ym_aig_obj_d>
  $<TARGET_OBJECTS:ym_bnet_obj_d>
  $<TARGET_OBJECTS:ym_fraig_obj_d>
  DEFINITIONS
  "-DDATAPATH=\"${DATA_DIR}\""
  )
