import React from 'react';
export const PrpeleafEditorGlobalContext = React.createContext({
	isReadOnly: false,
	changeText: () => {},
});
