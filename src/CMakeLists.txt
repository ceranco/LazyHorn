set (EXT_LIBRARIES ${Z3_LIBRARY})

add_executable(lh main.cpp Stats.cpp Global.cpp)

target_link_libraries (
	lh 
	${EXT_LIBRARIES} 
	${Boost_PROGRAM_OPTIONS_LIBRARY} 
	m 
	dl 
	pthread 
	z  
	stdc++ 
	${RT_LIB}
	${MISTRAL_LIBRARIES})

if (IH_STATIC_EXE)
    set (CMAKE_EXE_LINKER_FLAGS "-static -static-libgcc -static-libstdc++")
    set_target_properties (lh PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (lh PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()
#add_subdirectory(src)


